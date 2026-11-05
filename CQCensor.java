/*
 * Click nbfs://nbhost/SystemFileSystem/Templates/Licenses/license-default.txt to change this license
 * Click nbfs://nbhost/SystemFileSystem/Templates/Classes/Class.java to edit this template
 */
package cqcensors;

import cqcensors.fol.*;
import cqcensors.policy.EpistemicDependency;
import cqcensors.policy.DependencyGraph;
import cqcensors.policy.OntologyConjunctiveQuery;
import cqcensors.parser.ParserException;
import cqcensors.fol.Term.TermTypeException;
import java.net.URISyntaxException;

import org.semanticweb.owlapi.model.*;
import java.util.*;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;


import static cqcensors.QueryChecker.loadEDPolicyFromJson;
import static cqcensors.QueryChecker.rewriteEDPolicyWrtTbox;
import static cqcensors.util.OntologyUtils.loadOntology;
import static cqcensors.Increment.Increment_all;
import static cqcensors.Increment.Increment_all_non_zeros;
import static cqcensors.SPARQLParser.SPARQL_parser;
import static cqcensors.policy.EpistemicDependency.IND_AUX_PRED_NAME;
import static cqcensors.fol.MostGeneralUnifier.findMGU;




public class CQCensor {
    
    Configuration configuration; 
    String queryFilePath; 
    static OWLOntology tbox; 
    static Set<EpistemicDependency> policy; 
    static Set<EpistemicDependency> policyExpWrtTBox;	// ← policy expanded w.r.t. the TBox
    static Set<EpistemicDependency> policyExp; 			// ← policy expanded w.r.t. TBox and itself
    private static String ONTOLOGY_IRI;
    
    public CQCensor(Configuration config) throws OWLOntologyCreationException, ParserException, Term.TermTypeException, IOException, PredicateAtom.PredicateArityException, URISyntaxException {
        configuration = config; 
        queryFilePath = config.prependInputPath(config.queryFilename);
        
        ONTOLOGY_IRI = config.ontologyIRI;
               
        // Load the policy from the JSON file 
        policy = loadEDPolicyFromJson(config.prependInputPath(config.policyFilename), 
                config.prependInputPath(config.ontologyFilename));
        
        Logger.info("Policy P: " + policy);
        
        
        // Load OWL ontology
        tbox = loadOntology(config.prependInputPath(config.ontologyFilename)); 
        
        Logger.info("TBox T: " + tbox);
        
        // Check policy's acyclicity w.r.t. the TBox
        if (isAcyclicPolicy(policy, tbox)) {
            Logger.info("ACYCLIC POLICY OF SIZE: " + policy.size());
        }
        else {
            Logger.error("POLICY NOT ACYCLIC, EXITING ..."); // Maybe should raise an ERROR
        }
        
        /*
         * POLICY EXPANSION
         */
        
        System.out.println("Expanding policy w.r.t. TBox");
        policyExpWrtTBox = rewriteEDPolicyWrtTbox(policy, tbox);
        // Logger.info("Policy Expanded w.r.t. TBox: " + expandedwrtTBox);
        for (EpistemicDependency ed: policyExpWrtTBox) {
        	System.out.println(ed);
        }
        
        System.out.println("Expanding policy w.r.t. TBOX and itself");
        policyExp = expandAcyclicPolicy(policy, tbox);
        
        for (EpistemicDependency ed: policyExp) {
        	System.out.println(ed);
        }
        
        System.out.println("\n");
        
        CompleteCons(policyExp);
        
        //ComputeClashQueries(policyExp);
        
    }
    
    
    private HashSet<EpistemicDependency> expandAcyclicPolicy(Set<EpistemicDependency> policy, OWLOntology ontology) throws Term.TermTypeException, PredicateAtom.PredicateArityException, URISyntaxException {
    	Logger.info("ACYCLIC EXPANSION"); 
    	/*
    	 * We proceed in two steps:
    	 * 		1. Expand P w.r.t. T and get P'
    	 * 		2. Expand P' w.r.t. itself
    	 */
    	
    	// STEP 1
    	
    	Set<EpistemicDependency> tgdPolicySet = new HashSet<>();
    	for (EpistemicDependency ed: policy) {
    		tgdPolicySet.add(ed.createCorrespondingTGD(ONTOLOGY_IRI));
    	}
    	
    	Set<EpistemicDependency> intermediatePolicySet = rewriteEDPolicyWrtTbox(tgdPolicySet, ontology);
    	Set<EpistemicDependency> intermediatePolicySetWithoutInd = new HashSet<>();
        for (EpistemicDependency ed : intermediatePolicySet){
            intermediatePolicySetWithoutInd.add(ed.removePredicateFromBody(IND_AUX_PRED_NAME));
        }
    	
        
        // STEP 2
        return rewriteEDPolicyWrtItself(intermediatePolicySetWithoutInd);
    
    }
    
    private HashSet<EpistemicDependency> rewriteEDPolicyWrtItself(Set<EpistemicDependency> policy) throws Term.TermTypeException, PredicateAtom.PredicateArityException, URISyntaxException {
        HashSet<EpistemicDependency> res = new HashSet<>(policy);
        int oldsize = res.size();
        int newsize = oldsize+1;
        while(newsize > oldsize){
            res = expansionRound(res);
            oldsize = newsize;
            newsize = res.size();
        }
        return res;
    }

    private HashSet<EpistemicDependency> expansionRound(HashSet<EpistemicDependency> policy) throws Term.TermTypeException, PredicateAtom.PredicateArityException, URISyntaxException {
        // ArrayList<EpistemicDependency> res = new ArrayList<>(policy);
    	HashSet<EpistemicDependency> res = new HashSet<>(policy);
        for (EpistemicDependency ed1Original : policy){
            if (ed1Original.isDenial()) continue;
            for (EpistemicDependency ed2Original : policy){
                //Renaming to prevent undesired matchings
                EpistemicDependency ed1 = ed1Original.changeAllVariablesNames("ed1");
                EpistemicDependency ed2 = ed2Original.changeAllVariablesNames("ed2");
                //Prepare the PredicateAtoms for attempting a macthing
                Set<OntologyPredicateAtom> paSet2 = ed2.getBody().getOntologyPredicateAtoms();
                PredicateAtom head1 = ed1.getHead().getPredicateAtoms().iterator().next();
                head1.unbindVariables();
                for (OntologyPredicateAtom pa2 : paSet2){
                    //Look for a substitution that unifies a predicate atom of ed2 with the head of ed1
                    pa2.unbindVariables();
                    PredicateAtom[] arg = new PredicateAtom[2];
                    arg[0] = head1;
                    arg[1] = pa2;
                    Substitution mgu = findMGU(arg);
                    if (mgu != null){
                        //Apply the unificator to both eds, so that variables are unified in body, head and UQVs
                        EpistemicDependency ed1s = mgu.applyToED(ed1);
                        EpistemicDependency ed2s = mgu.applyToED(ed2);
                        OntologyPredicateAtom pa2s = mgu.applyToOntologyPredicateAtom(pa2);
                        //Create the new ED -- newBody
                        Set<OntologyPredicateAtom> newBodyAtomsTemp = ed2s.getBody().getOntologyPredicateAtoms();
                        Set<OntologyPredicateAtom> newBodyAtoms = new HashSet<>();
                        //The copy is necessary for HashSet.remove to work
                        for (OntologyPredicateAtom opa : newBodyAtomsTemp) {
                            opa.unbindVariables();
                            if(!opa.equals(pa2s)) newBodyAtoms.add(opa);
                        }
                        Set<OntologyPredicateAtom> temp = ed1s.getBody().getOntologyPredicateAtoms();
                        for(OntologyPredicateAtom opa : temp) opa.unbindVariables();
                        newBodyAtoms.addAll(temp);
                        //newHead
                        Set<OntologyPredicateAtom> newHeadAtoms = ed2s.getHead().getOntologyPredicateAtoms();
                        for(OntologyPredicateAtom opa : newHeadAtoms) opa.unbindVariables();
                        //newUQV
                        ArrayList<Variable> newUQV = ed2s.getUniversallyQuantifiedVariables();
                        newUQV.addAll(ed1s.getUniversallyQuantifiedVariables());
                        HashSet<Variable> tempSet = new HashSet<>(newUQV);
                        newUQV = new ArrayList<>(tempSet);

                        OntologyConjunctiveQuery newBody = new OntologyConjunctiveQuery(newBodyAtoms, newUQV);
                        //Manage denials
                        OntologyConjunctiveQuery newHead;
                        if (newHeadAtoms.isEmpty()) {
                            newHead = new OntologyConjunctiveQuery(new HashSet<>(Arrays.asList(new False())), newUQV);
                        }
                        else{
                            newHead = new OntologyConjunctiveQuery(newHeadAtoms, newUQV);
                        }

                        EpistemicDependency newEDOriginal = new EpistemicDependency(newBody, newHead, newUQV);
                        EpistemicDependency newED = newEDOriginal.changeAllVariablesNames(null); //restore nice names
                        if (!containsED(res, newED)) res.add(newED);
                        
                    }
                }
            }
        }
        return res;
    }

    //Set containment using ED.isEquivalent instead of equals
    private boolean containsED(HashSet<EpistemicDependency> policy, EpistemicDependency ed) {
        for (EpistemicDependency p : policy){
            if (p.isEquivalentTo(ed)) return true;
        }
        return false;
    }
    
    
    
    private boolean isAcyclicPolicy(Set<EpistemicDependency> policy, OWLOntology tbox) throws IOException {
        DependencyGraph dg = new DependencyGraph(policy, tbox); 
        return dg.isPolicyAcyclic();
    }
   
    
    
    private static class Result {
    	// Auxiliary class to store the results; 
    	
    	ArrayList<ArrayList<HashMap<Term,Term>>> homomorphisms; 
    	ArrayList<Integer> indexes; 
    	
    	private Result(ArrayList<ArrayList<HashMap<Term,Term>>> H, ArrayList<Integer> I) {
    		this.homomorphisms = H; 
    		this.indexes = I;
    	}
    }
    
    public Result compute_homomorphisms(ArrayList<OntologyPredicateAtom> body_atoms, Set<PredicateAtom> query_atoms, List<Variable> universally_quantified_vars) {
    	ArrayList<ArrayList<HashMap<Term, Term>>> H = new ArrayList<ArrayList<HashMap<Term, Term>>>();
    	
    	/* INPUT:
    	 * 	body_atoms: List of atoms occurring in the body of the considered epistemic dependency
    	 * 	query_atoms: atoms occurring in the query
    	 * 	universally_quantified_vars: universally quantified variables in the epistemic dependency
    	 * 	
    	 * OUTPUT:
    	 * 	indexes: an ArrayList to keep track of the indexes in body_atoms. 
    	 * 		We will use it to keep track of the atoms that we are considering for a given combination of homomorphism, 
    	 * 		precisely we store it's position (index) in the body of delta
    	 * 	homomorphisms: the homomorphisms found for each atom in body delta
    	 */
    	ArrayList<Integer> indexes = new ArrayList<>(); 
    	
    	
    	int index = 0;
    	for (OntologyPredicateAtom b_a: body_atoms) {
    		ArrayList<HashMap<Term, Term>> homomorphisms = new ArrayList<HashMap<Term, Term>>();
    		for (PredicateAtom q_a: query_atoms) {
    			if (b_a.getPredicateName().equals(q_a.getPredicateName()) && b_a.getArity() == q_a.getArity()) {
    				HashMap<Term, Term> h = new HashMap<>();
    				
    				Term b_t1 = b_a.getTerm(0);		// term 1 of the body's atom
    				Term q_t1 = q_a.getTerm(0);		// term 1 of the query's atom

    				
    				if (q_t1 instanceof Variable && universally_quantified_vars.stream().anyMatch(v -> v.getName().equals(((Variable) b_t1).getName()))) {
    				//if (universally_quantified_vars.contains(b_t1) && q_t1 instanceof Variable) {
    					// Can't map a free variable onto an existential variable
    					continue;
    				}
    				else if (b_t1 instanceof DataConstant && !(q_t1 instanceof DataConstant)) {
    					// a homomorphisms preservers the constants
    					continue;
    				}
    				else if (b_t1 instanceof DataConstant && q_t1 instanceof DataConstant && !(b_t1.equals(q_t1))) { 
    					// again a homomorphisms preserves the constants; a constant can be mapped only to itself
    					continue;
    				}
    				else {
    					h.put(b_t1, q_t1);
    				}
    				
    				// If arity = 2 we need to consider also the second term
    				if (b_a.getArity() == 2) {
    					Term b_t2 = b_a.getTerm(1);
    					Term q_t2 = q_a.getTerm(1);
    					
    					if (universally_quantified_vars.stream().anyMatch(v -> v.getName().equals(((Variable) b_t2).getName())) && q_t2 instanceof Variable) {
    						continue;
    					}
    					else if (b_t2 instanceof DataConstant && !(q_t2 instanceof DataConstant)) {
        					continue;
        				}
        				else if (b_t2 instanceof DataConstant && q_t2 instanceof DataConstant && !(b_t2.equals(q_t2))) {
        					continue;
        				}
    					else  {
    						h.put(b_t2, q_t2);
    					}
    				}
    				
    				homomorphisms.add(h);
    			}
    			
    		}
    		if (!homomorphisms.isEmpty()) {
    			H.add(homomorphisms);
    			indexes.add(index);
    		}
    		index += 1;
    			
    		
    	}
    	
    	Result res = new Result(H, indexes);
    	
    	return res;
    	
    }
        
    
    
    /*
    Algorithm: ComputeClashQueries
        - Input: ED-closed policy P, A BCQ q
        - Output: A set of CQs
    */
    
    // Maybe: public Set<ConjunctiveQuery>
	public Set<OntologyConjunctiveQuery> ComputeClashQueries(Set<EpistemicDependency> policy) throws IOException{
        
        Set<OntologyConjunctiveQuery> Q = new HashSet<>();
        
        // parse the query
        String sparql_query = "";
        try {
            sparql_query = Files.readString(Path.of(queryFilePath));
            Logger.info("Read SARQL_query: \n" + sparql_query);
            
            
        } catch(IOException e) {
        	Logger.error("Query not found: " + e.getMessage());
        }
        
        // Retrieve the set of Atoms in the sparql query
        Set<PredicateAtom> sparql_query_atoms = SPARQL_parser(sparql_query);
        Logger.info("Parsed sparql_query, found atoms: " + sparql_query_atoms);
        
        for (EpistemicDependency ed: policy) {
        	OntologyConjunctiveQuery body = ed.getBody();
        	
        	Logger.info("ED body: " + body);
 
        	
        	ArrayList<Variable> universally_quantified_vars = ed.getUniversallyQuantifiedVariables();
        
        	
        	Set<OntologyPredicateAtom> atoms = body.getAllPredicateAtoms();
        	// We store everything in an ArrayList, since we'll need to preserve the order
        	ArrayList<OntologyPredicateAtom> ED_atoms = new ArrayList<>();
        	for (OntologyPredicateAtom a: atoms) {
        		ED_atoms.add(a);        	
        	}
        	
        	// Compute the homomorphisms from the atoms in the body of the ED
        	// to the atoms of the query
        	Result ris = compute_homomorphisms(ED_atoms, sparql_query_atoms, universally_quantified_vars);
        	
        	ArrayList<ArrayList<HashMap<Term, Term>>> homomorphisms = ris.homomorphisms;
        	ArrayList<Integer> indexes = ris.indexes;
        	
        	
        	Logger.info("Found homomoprhisms: " + homomorphisms);
        	
        	int l = homomorphisms.size();
        	if (l == 0) continue; // No homomorphisms for this epistemic dependency
        	
        	// We compute K, an array storing the counter of the number of homomorphisms 
        	// found for each atom (except those for which the count is zero.
        	ArrayList<Integer> K = new ArrayList<>();
        	
        	for (ArrayList<HashMap<Term, Term>> a: homomorphisms) {
        		K.add(a.size());
        	}
        	
        	
        	// Initialization of the matrix (or hashmap) M 
        	
        	ArrayList<Integer> A = new ArrayList<>();
        	for (int j = 0; j < l; j++) {
        		A.add(0);
        	}
        	HashMap<ArrayList<Integer>, Integer> M = initialize_map(A, K, l);
        	
        	
        	
        	/*
        	 * EXPLORE: Next we explore all the possible combinations of homomorphisms to keep
        	 * 			just the admissible ones.
        	 */
        	ArrayList<Integer> A_init = new ArrayList<>();
        	// Initialize Ainit with all 1s
        	for (int i = 0; i < l; i++) {
        		A_init.add(1); 
        	}
        	
        	ArrayList<Integer> A1 = new ArrayList<>(A_init);
        	ArrayList<Integer> A2 = new ArrayList<>();
        	
        	
        	do {
	        	M = CheckClash(ED_atoms, homomorphisms, A1, M, l, indexes);
	        	A2 = new ArrayList<>(A1); 
	        	A1 = Increment_all_non_zeros(A1, K);  	
        	} while (!A1.equals(A2));
        	
        	
        	
        	Logger.info("Final state of M: " + M);
        	
        	
        	/*
        	 * Generate the candidate clash queries
        	 */
        	
        	int num_atoms = ED_atoms.size();
        	
            for (var entry: M.entrySet()) {
            	
            	
            	if (entry.getValue() == 1) {
            		ArrayList<Integer> key = entry.getKey();
                	
            		// List of the atoms in the body not considered by the homomorphism
            		ArrayList<OntologyPredicateAtom> QDiff = new ArrayList<OntologyPredicateAtom>();
            		for (int i = 0; i < num_atoms; i++) {
                		if (!indexes.contains(i)) {
                			// I contains only the indexes of the atoms for which
                			// we found at least one homomorphism
                			QDiff.add(ED_atoms.get(i));
                		}
                	}
            		
                	
                	for (int i = 0; i < l; i++) {
                		if (key.get(i) == 0) {
                			QDiff.add(ED_atoms.get(indexes.get(i)));
                		}
                	}
            		
                	ArrayList<HashMap<Term, Term>> sigma = new ArrayList<HashMap<Term, Term>>();
                	for (int i = 0; i < l; i++) {
                		if (key.get(i) > 0) {
                			sigma.add(homomorphisms.get(i).get(key.get(i)-1));	// H[1][A[1] \cup ... \cup H[l]A[l]
                		}
                	}
                	
                	HashSet<PredicateAtom> cq_atoms = new HashSet<>();
                	
                	
                	List<Variable> free_vars = new ArrayList<>(ed.getUniversallyQuantifiedVariables()); // Need them to build the Conjunctive Query
                	
                	// For each atom not mapped by the current choice of homomorphisms,
                	// we see if we can apply h to some of its terms.
                	for (OntologyPredicateAtom a: QDiff) {
                		
                		ArrayList<Term> atom_terms = new ArrayList<>(a.getTerms());		// get the original terms; then we will replace them in case they are mapped by h
                		
                		for (HashMap<Term,Term> h: sigma) {
                			for (var e: h.entrySet()) {
                				int i = 0;	// → to keep track of the index of the term (can be 0 or 1)
                				for (Term t: a.getTerms()) {
                					
                					if (t.equals(e.getKey())) {
                						atom_terms.set(i, e.getValue());	// replace the term with the one mapped by the homomorphism
                						if (t instanceof Variable) {
                							Variable x = new Variable(((Variable) t).getName());
                							x.unbind();
                							if (free_vars.contains(x)) {
	                							free_vars.remove(x);
                							}
                						}
                					}
                					i += 1;
                				}
                				
                			}
                		}
                		
                		
                		cq_atoms.add(new PredicateAtom(a.getPredicateName(), atom_terms));
                		
                	}
                	
                	try {
                		
						OntologyConjunctiveQuery cq = new OntologyConjunctiveQuery(cq_atoms, free_vars);
						Logger.info("Adding candidate clash query: " + cq);
						Q.add(cq);
						
					} catch (TermTypeException e) {
						Logger.error("Term Type Error" + e.getMessage());
						//e.printStackTrace();
					}
                	
            		
            	}
            }
        
        }
        
        Logger.info("Candidate Clash Queries: \n" + Q);
        
        return Q;
        
    }
    
    
    private HashMap<ArrayList<Integer>, Integer> initialize_map(ArrayList<Integer> A, ArrayList<Integer> K, int l) {
    	
    	/*
    	 * Auxiliary method to initialize the Map M containing the possible combinations of homomorphisms
    	 * At the beginning everything is initialized with 1s (since every combination of homomorphisms is 
    	 * potentially admissible) except for M[0,...,0] that is set to 0 since it corresponds to body of delta
    	 */
    	
    	HashMap<ArrayList<Integer>, Integer> M = new HashMap<ArrayList<Integer>, Integer>(); 
    	
    	M.put(A, 0); // M[0,...,0] = 0 since it corresponds to the body
    	
    	ArrayList<Integer> A1 = new ArrayList<>(A); 
    	ArrayList<Integer> A2 = new ArrayList<>();
    	
    	// Initialize A2 with -1s
    	for (int i = 0; i < l; i++) {
    		A2.add(-1);
    	}
    	
    	while (!A1.equals(A2)) {
    		A2 = new ArrayList<>(A1);
    		A1 = Increment_all(A1, K);
    		M.putIfAbsent(A1, 1);
    	}
    	
    	return M; 
    }
    
    
    private HashMap<ArrayList<Integer>, Integer> CheckClash(ArrayList<OntologyPredicateAtom> ED_atoms, ArrayList<ArrayList<HashMap<Term, Term>>> H, 
    														ArrayList<Integer> A, HashMap<ArrayList<Integer>, Integer> M, int l, ArrayList<Integer> I) {
    	/*
    	 * H: An ArrayList of ArrayLists storing the homomorphisms for each atom
    	 * A: an array representing the choice of homomorphisms
    	 * M: the HashMap where the keys represent the choices of homomorphisms, and the value is 1, if that given choice is admissible, 0 otherwise.
    	 * l: the size of A
    	 * I: indexes
    	 */
    	
    	
    	//ArrayList<HashMap<Term, Term>> sigma = new ArrayList<HashMap<Term, Term>>();
    	HashMap<Term, Term> sigma = new HashMap<>();
    	
    	
    	// Initialize the array QDiff containing the atoms not mapped by H
    	
    	int num_atoms = ED_atoms.size();
    	
    	ArrayList<OntologyPredicateAtom> QDiff = new ArrayList<>();
    	
    	for (int i = 0; i < num_atoms; i++) {
    		if (!I.contains(i)) {
    			// I contains only the indexes of the atoms for which
    			// we found at least one homo
    			QDiff.add(ED_atoms.get(i));
    		}
    	}
    	
    	for (int i = 0; i < l; i++) {
    		if (A.get(i) == 0) {
    			QDiff.add(ED_atoms.get(I.get(i)));
    		}
    	}
    	
    	
    	/*
    	 * CHECK ADIMISSIBILITY
    	 * Sigma is admissible if it passes the following two checks:
    	 *     -1: it is a homomorphism
    	 *     -2: if x is a variable occurring in the domain of sigma and sigma(x) is a variable. 
    	 *         then x does not appear in Atoms(ED) minus dom(sigma).
    	 */
    	
    	boolean adm = true;
    	
    	for (int i = 0; i < l; i++) {
    		if (A.get(i) > 0) {
    			for (var entry: H.get(i).get(A.get(i)-1).entrySet()) {
    				if (!(sigma.putIfAbsent(entry.getKey(), entry.getValue()) == null)) {
    					// if putIfAbsent does not return null then the key was already present
    					if (!(entry.getValue().equals(sigma.get(entry.getKey())))) {
    						// Trying to map a variable to two different values, this is not even a homomorphism !!
    						// Fist condition of admissibility not satisfied
    						adm = false;
    						break;
    						
    					}
    				}
    				
    			}
    			
    		}
    		if (!adm) break;
    	}
    	
    	
    	if (adm) {
	    	for (var map: sigma.entrySet()) {
	    		// Need to check second condition
	    		if (map.getValue() instanceof Variable) {
	    			Variable v = (Variable) map.getKey();
	    			for (OntologyPredicateAtom oa: QDiff) {
	    				if (oa.getFreeVariables().contains(v)) {
	    					adm = false; 
	    					break;
	    				}
	    			}
	    		}
	    		if (!adm) break;
	    		
	    	}
    	}
    	
    	
    	if (!adm) {
    		M.replace(A, 0);	// Set the entry M[A] = 0;
    	}
    	
    	
    	/*
    	 * OPTIMIZATION: If admissible and sigma does not assign any variable occurring in QDiff, then SkipSubsets
    	 */
    	
    	if (adm) {
			boolean assigned = false;
			for (Term key: sigma.keySet()) {
				for (OntologyPredicateAtom oa: QDiff) {
					if (oa.hasVariable((Variable) key)) {
						//Logger.info("Found Assignment");
						assigned = true;
						break;
					}
				}
				
				if (assigned) {
					break;
				}
			}
			
			if (!assigned) {
				Logger.info("Calling SkipSubsets for choice A: " + A);
				M = SkipSubsets(A, M, l);
				return M;
				
			}
    	}
    	
    	
    	
    	int counter = 0;
    	for (int i = 0; i < l; i++) {
    		if (A.get(i) > 0) {
    			counter += 1; 
    			if (counter > 1) break;
    		}
    	}
    	
 
    	if (counter < 2) {
    		// Nothing to explore, return
    		return M;
    	}
    	
    	
    	// Still subsets to explore
    	for (int i = 0; i < l; i++) {
    		if (A.get(i) != 0) {
				ArrayList<Integer> A1 = new ArrayList<>(A);
    			A1.set(i, 0);
    		
    			if ((int) M.get(A1) != 0) {
    				
    				M = CheckClash(ED_atoms, H, A1, M, l, I);
    			}
    		}
    	}
    	
    	
    	return M;
    	
    }
    
    
    private HashMap<ArrayList<Integer>, Integer> SkipSubsets(ArrayList<Integer> A, HashMap<ArrayList<Integer>, Integer> M, int l) {
    	for (int i = 0; i < l; i++) {
    		if (A.get(i) != 0) {
    			ArrayList<Integer> A1 = new ArrayList<>(A);
    			A1.set(i, 0);
    			M.replace(A1, 0);
    			M = SkipSubsets(A1, M, l);
    		}
    	}
    	
    	return M;
    	
    }
    
    
    /*
     * 	POLICY CONSEQUENCES ALG
     */
    
    // OntologyConjunctiveQuery
    private void CompleteCons(Set<EpistemicDependency> policy) {	//	, OntologyConjunctiveQuery q, HashMap<Term, Term> sigma) {
    	HashSet<OntologyConjunctiveQuery> C = new HashSet<>();
    	
    	/*
    	do {
    		HashSet<OntologyConjunctiveQuery> C_aux = new HashSet<>();
    		
    		for (EpistemicDependency ED: policy) {
    			
    		}
    	}
    	*/
    	
    	// parse the query
        String sparql_query = "";
        try {
            sparql_query = Files.readString(Path.of(queryFilePath));
            Logger.info("Read SARQL_query: \n" + sparql_query);
            
            
        } catch(IOException e) {
        	Logger.error("Query not found: " + e.getMessage());
        }
    	
    	// Retrieve the set of Atoms in the sparql query
        Set<PredicateAtom> sparql_query_atoms = SPARQL_parser(sparql_query);
        Logger.info("Parsed sparql_query, found atoms: " + sparql_query_atoms);
    	
    	for (EpistemicDependency ed: policy) {
    		OntologyConjunctiveQuery body = ed.getBody();
    		
    		Logger.info("ED body: " + body);
    		
    		ArrayList<Variable> universally_quantified_vars = ed.getUniversallyQuantifiedVariables();
    		
    		Set<OntologyPredicateAtom> atoms = body.getAllPredicateAtoms();
        	// We store everything in an ArrayList, since we'll need to preserve the order
        	ArrayList<OntologyPredicateAtom> ED_atoms = new ArrayList<>();
        	for (OntologyPredicateAtom a: atoms) {
        		ED_atoms.add(a);        	
        	}
        	
        	ArrayList<HashMap<Term, Term>> simple_homos = simple_homomorphism(ED_atoms, sparql_query_atoms, universally_quantified_vars);
        	
        	Logger.info("Found simple homomorphisms" + simple_homos);
    		
    	}
    	
    	return;
    }
    
    
    private ArrayList<HashMap<Term, Term>> simple_homomorphism(ArrayList<OntologyPredicateAtom> body_atoms, Set<PredicateAtom> query_atoms, List<Variable> universally_quantified_vars) {
    	/*
    	 * INPUT:
    	 * 		body_atoms: List of atoms occurring in the epistemic dependency
    	 * 		query_atoms: atoms occurring in the query
    	 * 
    	 * OUTPUT:
    	 * 		a simple homomorphism from body_atoms to query_atoms
    	 */
    	
    	ArrayList<HashMap<Term, Term>> h = new ArrayList<>(); 
    	
    	Result res = compute_homomorphisms(body_atoms, query_atoms, universally_quantified_vars);
    	
    	ArrayList<ArrayList<HashMap<Term, Term>>> homomorphisms = res.homomorphisms;
    	ArrayList<Integer> indexes = res.indexes;
    	
    	
    	int l = homomorphisms.size();
    	
    	
    	// A simple homomorphism maps all the atoms of the body. If some of 
    	// these are not mapped, then we return the empty
    	if (l < body_atoms.size())
    		return h;
    	
    	if (l > 1) {
    		// Initialize an array of l 1's
    		ArrayList<Integer> A_init = new ArrayList<>(); 
    		for (int i = 0; i < l; i++) {
    			A_init.add(1);
    		}
    		
    		// We compute K, an array storing the counter of the number of homomorphisms 
        	// found for each atom
        	ArrayList<Integer> K = new ArrayList<>();
        	
        	for (ArrayList<HashMap<Term, Term>> a: homomorphisms) {
        		K.add(a.size());
        	}
        	
        	ArrayList<Integer> A = new ArrayList<>(A_init);
        	ArrayList<Integer> A_aux = new ArrayList<>();
        	
        	do {
        	
		    	// Compute the valid combinations of homomorphisms
		    	HashMap<Term, Term> sigma = new HashMap<>();
		    	
		    	boolean valid = true;
		    	
		    	for (int i = 0; i < l; i++) {
		    		for (var entry: homomorphisms.get(i).get(A.get(i)-1).entrySet()) {
		    			if (!(sigma.putIfAbsent(entry.getKey(), entry.getValue()) == null)) {
		    				// If putIfAbsent does not return null, then the key was already present
		    				// In this case we need to check that we are not mapping the same variable to two different values
		    				if (!(entry.getValue().equals(sigma.get(entry.getKey())))) {
		    					// This is not a valid homomorphism
		    					valid = false;
		    					break;
		    				}
		    			}
		    		}
		    		if (!valid) break;
		    	}
		    	
		    	if (valid) {
		    		h.add(sigma);
		    	}
		    	
		    	// Increment
		    	A_aux = new ArrayList<>(A);
		    	A = Increment_all_non_zeros(A, K);
		    	
        	} while(!A.equals(A_aux));
		    	
    		
    	} else {

    		h.add(homomorphisms.get(0).get(0));
    	}
    	
    	return h;
    	
    	
    }
    
}
