/*
 * Click nbfs://nbhost/SystemFileSystem/Templates/Licenses/license-default.txt to change this license
 * Click nbfs://nbhost/SystemFileSystem/Templates/Classes/Class.java to edit this template
 */
package cqcensors;

import cqcensors.fol.*;
import cqcensors.fol.DataConstant.DatatypeNoMatchException;
import cqcensors.fol.PredicateAtom.PredicateArityException;
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

import cqcensors.fol.OntologyPredicateAtom.Type;


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
        
        
        //System.out.println("Expanding policy w.r.t. TBox");
        policyExpWrtTBox = rewriteEDPolicyWrtTbox(policy, tbox);
        // Logger.info("Policy Expanded w.r.t. TBox: " + expandedwrtTBox);
        /*
        for (EpistemicDependency ed: policyExpWrtTBox) {
        	System.out.println(ed);
        }
        */
        
        //System.out.println("Expanding policy w.r.t. TBOX and itself");
        policyExp = expandAcyclicPolicy(policy, tbox);
        
        /*
        for (EpistemicDependency ed: policyExp) {
        	System.out.println(ed);
        }
        */
        
        
        
        
        
        /*
         * POLICY CONSEQUENCES TESTS
         */
         
        //System.out.println("\n");
        
        Map<Term, Term> sigma = new HashMap<>();
        
        Variable v1 = new Variable("x");
        Variable v2 = new Variable("y");
        ObjectConstant c = new ObjectConstant("c");
 
        
        
        List<Term> terms1 = new ArrayList<>(); 
        terms1.add(v1);
        terms1.add(v2);
        
        List<Term> terms2 = new ArrayList<>(); 
        terms2.add(v2);
        terms2.add(c);
        //List<Constant> constants = new ArrayList<>();
        /*
        try {
			DataConstant c = new DataConstant("c");
			terms2.add(c);
			constants.add(c);
		} catch (DatatypeNoMatchException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		*/
        
        // R(x,y) and S(y, c)
        OntologyPredicateAtom opa1 = new OntologyPredicateAtom("R", terms1); //, Type.ROLE);
        OntologyPredicateAtom opa2 = new OntologyPredicateAtom("S", terms2); //, Type.ROLE);
        
        List<OntologyPredicateAtom> atoms = new ArrayList<>();
        atoms.add(opa1);
        atoms.add(opa2);
        
        List<Variable> free_vars = new ArrayList<>();
        free_vars.add(v1);
        free_vars.add(v2);
        
        OntologyConjunctiveQuery q = new OntologyConjunctiveQuery(atoms, free_vars);
        
        //Logger.info("Ontology CQ: " + q);
        
        List<Map<Term, Term>> maps = new ArrayList<>();
        //maps = computePrecondition(free_vars, constants, sigma);
        
        
        //Logger.info("Unidirectional mappings \n: " + maps);
        
        Map<OntologyConjunctiveQuery, Map<Term, Term>> S = PolicyCons(policyExpWrtTBox, q, sigma);
        
        Logger.info("S: " + S);
        
        //CompleteCons(policyExpWrtTBox, sigma);
        
        //ComputeClashQueries(policyExp);
        
    }
    
    
    private HashSet<EpistemicDependency> expandAcyclicPolicy(Set<EpistemicDependency> policy, OWLOntology ontology) throws Term.TermTypeException, PredicateAtom.PredicateArityException, URISyntaxException {
    	//Logger.info("ACYCLIC EXPANSION"); 
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
    
    public Result compute_homomorphisms(ArrayList<OntologyPredicateAtom> body_atoms, Set<OntologyPredicateAtom> query_atoms, List<Variable> universally_quantified_vars) {
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
	public Set<OntologyConjunctiveQuery> ComputeClashQueries(Set<EpistemicDependency> policy) throws IOException, URISyntaxException, PredicateArityException, TermTypeException{
        
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
        Set<OntologyPredicateAtom> sparql_query_atoms = SPARQL_parser(sparql_query);
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
                		
                		
                		cq_atoms.add(new OntologyPredicateAtom(a.getPredicateName(), atom_terms));
                		
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
    
    // @SuppressWarnings({ "unlikely-arg-type", "unlikely-arg-type" })
	private List<Map<Term, Term>> computePrecondition(List<Variable> free_vars, List<Constant> constants) { //,  Map<Term, Term> sigma) {
    	
    	/*
    	 * INPUT: 
    	 * 	- free_vars: free variables of candidate clash query
    	 *  - constants: constants in the candidate clash query
    	 * 	- sigma: mapping of the variables
    	 * 
    	 * OUTPUT:
    	 * 	- returns the set of relevant mappings of the free variables in sigma(q) to the free variables and constants of sigma(q)
    	 * 		NOTE: Each mapping cannot be the identity
    	 */
    	List<Map<Term,Term>> mappings = new ArrayList<>();
    
    	
    	Map<Term, List<Term>> UM = new HashMap<>(); 	// HashMap for storing the unidirectional mappings
    	
    	
    	/*
    	 * First, map the free vars to the free vars, avoiding mapping a 
    	 * variable to itself and symmetric mappings, i.e. mappings of the 
    	 * kind { x → y } and { y → x }.
    	 * Second, map the free vars to constants
    	 */
    	for (Variable v1: free_vars) {
    		for (Variable v2: free_vars) {
    			if (!v1.equals(v2) && !(UM.containsKey(v2) && UM.get(v2).contains(v1))) {
    				if (!UM.containsKey(v1)) {
    					List<Term> L = new ArrayList<>();
    					L.add(v2);
    					UM.put(v1, L);
    				}
    				else {
    					if (!UM.get(v1).contains(v2)) {
    						UM.get(v1).add(v2);
    					}
    				}
    				
    			}
    		}
    		
    		// Now is the turn of the constants
    		for (Constant c: constants) {
    			if (!UM.containsKey(v1)) {
    				List<Term> L = new ArrayList<>(); 
    				L.add(c);
    				UM.put(v1, L);
    			}
    			else {
    				if (!UM.get(v1).contains(c)) {
    					UM.get(v1).add(c);
    				}
    			}
    		}
    		
    	}
    	
    	/*
    	 * Compute the relevant combinations of mappings
    	 * 	1. We start by putting in 'mappings' the unidirectional mappings computed at the previous step
    	 *  2. We compute the relevant combinations of these unidirectional mappings
    	 */
    	
    	
    	int l = UM.size();
    	ArrayList<Integer> A = new ArrayList<>(); 
    	
    	// Initialize A with l 0s
    	for (int i = 0; i < l; i++) {
    		A.add(0);
    	}
    	ArrayList<Integer> A1 = new ArrayList<>(A);
    	
    	// Initialize an array K storing the number of values for each key
    	ArrayList<Integer> K = new ArrayList<>(); 
    	
    	for (var entry: UM.entrySet()) {
    		K.add(entry.getValue().size());
    	}
    	
    	ArrayList<Term> keys = new ArrayList<>();
    	for (Term k: UM.keySet()) {
    		keys.add(k);
    	}
    	
    	ArrayList<Integer> A2 = new ArrayList<>();
    	
    	//Logger.info("K: " + K);
    	//Logger.info("Unidirectional mappings: " + UM);
    	
    	A1 = Increment_all(A1, K); // Skip the case [0, ..., 0]
    	
    	do {
    		A2 = new ArrayList<>(A1);
    		Map<Term, Term> map = new HashMap<>();
    		boolean relevant = true;
    		for (int i = 0; i < l; i++) {
    			if (A1.get(i) > 0) {
	    			if (!(map.values().contains(keys.get(i)) || map.containsKey(UM.get(keys.get(i)).get(A1.get(i)-1)))) {
	    				/*
	    				 * The if condition prevents two cases:
	    				 * 		1. {x → y}; then avoids putting y → c
	    				 * 		2. {y → c}; then it avoids putting x → y
	    				 */
	    				
	    				map.put(keys.get(i), UM.get(keys.get(i)).get(A1.get(i)-1));
	    				//Logger.warn("MAP: " + map);
	    			}
	    			else {
	    				relevant = false;
	    				continue;	// not a relevant mapping
	    			}
    			}
    		}
    		if (relevant) {
    			mappings.add(map);
    		}
    		A1 = Increment_all(A1, K);
    	} while (!A1.equals(A2));
    	
    	
    	return mappings;
    }
	
	

    
private OntologyConjunctiveQuery apply_sigma(OntologyConjunctiveQuery q, Map<Term, Term> sigma) throws URISyntaxException, PredicateArityException, TermTypeException {
    	
    	/*
    	 * Takes in input a set of atoms a mapping sigma
    	 * Returns a new set of atoms with variables replaced by the substitution in sigma
    	 */
	
		if (sigma.isEmpty()) {
			return q;
		}
	
		Set<OntologyPredicateAtom> atoms = q.getAllPredicateAtoms();
		ArrayList<Variable> free_vars = q.getFreeVariables();
    	
		ArrayList<Variable> unbounded_free_vars = new ArrayList<>();
		
		for (Variable v: free_vars) {
			Variable new_v = new Variable(v.getName());
			unbounded_free_vars.add(new_v);
		}
    	
    	// Unbound terms
    	Map<Term, Term> unbounded_sigma = new HashMap<>();
    	for (var e: sigma.entrySet()) {
    		if (e.getKey() instanceof Variable && e.getValue() instanceof Variable) {
    			Variable k = new Variable(((Variable) e.getKey()).getName());
    			Variable v = new Variable(((Variable) e.getValue()).getName());
    			unbounded_sigma.put(k, v);
    		}
    		
    		else if (e.getKey() instanceof Variable) {
    			Variable k = new Variable(((Variable) e.getKey()).getName());
    			unbounded_sigma.put(k, e.getValue());
    		}
    	}
    	
    	Set<PredicateAtom> mapped_atoms = new HashSet<>();
    	
    	for (OntologyPredicateAtom a: atoms) {
    		
    		// unbound terms
    		List<Term> terms = new ArrayList<>(a.getTerms());
    		//Logger.debug("Terms: " + terms);
    		List<Term> unbounded_terms = new ArrayList<>();
    		for (Term t: terms) {
    			if (t instanceof Variable) {
    				Variable v = new Variable(((Variable) t).getName());
    				//v.unbind();
    				unbounded_terms.add(v);
    			}
    			else {
    				unbounded_terms.add(t);
    			}
    		}
    		
    		// map variables
    		for (int i = 0; i < unbounded_terms.size(); i++) {
    			Term t = unbounded_terms.get(i);
    			if (t instanceof Variable) {
	    			if (unbounded_sigma.containsKey(t)) {
	    				Term t2 = unbounded_sigma.get(t); // t2 is the mapping term, i.e. t → t2
	    				unbounded_terms.set(i, t2);
	    				
	    				if (t2 instanceof ObjectConstant) {
	    					unbounded_free_vars.remove(t);	// if the mapping term is a constant, we simply remove it from the set of variables
	    				}
	    				else {
	    					// Since t2 is a variable, replace t with t2
	    					unbounded_free_vars.remove(t);
	    					if (!unbounded_free_vars.contains(t2)) {
	    						unbounded_free_vars.add((Variable) t2);
	    					}
	    				}
	    			}
    			}
	    	}
    		
    		mapped_atoms.add(new OntologyPredicateAtom(a.getPredicateName(), unbounded_terms));
    	}
 
    	
    	OntologyConjunctiveQuery mapped_query = new OntologyConjunctiveQuery(mapped_atoms, unbounded_free_vars);
    	
    	return mapped_query;
    	
    }
    
    
 
    public Map<OntologyConjunctiveQuery, Map<Term, Term>> PolicyCons(Set<EpistemicDependency> policy, OntologyConjunctiveQuery q, Map<Term, Term> sigma) throws URISyntaxException, PredicateArityException, TermTypeException{
    	        
    	
    	System.out.println("\n");
    	Logger.info("********* CALLING COMPLETE CONS ************");
    	
    	
    	OntologyConjunctiveQuery q_cons = CompleteCons(policy, q, sigma);
    	
    	System.out.println("\n\n");
    	Logger.info("********* RETURNING TO POLICY CONS ************");
    	
    	ArrayList<Variable> free_vars = q_cons.getFreeVariables();
    	Set<OntologyPredicateAtom> atoms = q_cons.getAllPredicateAtoms();
    	
    	
    	Map<OntologyConjunctiveQuery, Map<Term, Term>> S = new HashMap<>();	// S = {(q, sigma)}
    	S.putIfAbsent(q_cons, sigma);

    	
    	// Compute sigma(q)
    	
    	OntologyConjunctiveQuery sigma_q = apply_sigma(q_cons, sigma);
    	
    	ArrayList<Variable> sigma_q_free_vars = sigma_q.getFreeVariables();
    	
		List<Constant> cons = new ArrayList<>();
		
		for (Term c: sigma_q.getConstants()) {
			if (!cons.contains(c)) 
				cons.add((Constant) c);
		}
    	
    	Logger.warn("Sigma(Q) free vars: " + sigma_q_free_vars);
    	// Logger.error("Constants: " + cons);
    	// Compute the set of preconditions for computing a simple homomorphism
    	List<Map<Term, Term>> preconditions = computePrecondition(sigma_q_free_vars, cons);
    	
    	if (preconditions.get(0).isEmpty()) return S;
    	
    	Logger.debug("Preconditions: " + preconditions);
    	
    	for (Map<Term, Term> p: preconditions) {
    		for (EpistemicDependency ed: policy) {
    			
    			// Apply precondition p to the atoms of the mapped query, i.e. sigma(q)
    			
    			OntologyConjunctiveQuery p_q = apply_sigma(sigma_q, p);
    			Set<OntologyPredicateAtom> mapped_atoms = p_q.getAllPredicateAtoms();
    			Logger.debug("h'(q):" + p_q);
    			
    			
    			// Compute the simple homomorphisms from body(delta) to p(q)
    			
    			OntologyConjunctiveQuery body = ed.getBody();
    			Set<OntologyPredicateAtom> ED_body_atoms = body.getAllPredicateAtoms();
    			ArrayList<OntologyPredicateAtom> body_atoms = new ArrayList<>();
            	for (OntologyPredicateAtom a: ED_body_atoms) {
            		body_atoms.add(a);        	
            	}
            	
    			ArrayList<Variable> body_free_vars = ed.getUniversallyQuantifiedVariables();

    			// Finally compute the simple homomorphisms
    			ArrayList<HashMap<Term, Term>> simple_homos = simple_homomorphism(body_atoms, mapped_atoms, body_free_vars);
    			
    			if (simple_homos.isEmpty()) continue;	// If no simple homomorphism was found, then continue
    			
    			//Logger.info("\nFound simple homos: " + simple_homos);
    			//Logger.warn("Sigma: " + sigma);
    			
    			// If we found a simple homomorphisms, then extend the current sigma
				Map<Term, Term> new_sigma = new HashMap<>(sigma);
				new_sigma.putAll(p);
				Logger.warn("Sigma': " + new_sigma);
    			
    			for (HashMap<Term, Term> h: simple_homos) {
    				
    				// We check if we derive a new consequence
    				boolean new_head = false;
    				
    				// Compute head(h(delta)), i.e. apply homomorphism to the head of the epistemic dependency
    				OntologyConjunctiveQuery head = ed.getHead();
    				OntologyConjunctiveQuery mapped_head = apply_sigma(head, h);
    				Set<OntologyPredicateAtom> mapped_head_atoms = mapped_head.getAllPredicateAtoms();
    				
    				
    				Set<OntologyPredicateAtom> new_query_atoms = new HashSet<>(atoms);
    				
    				for (OntologyPredicateAtom opa: mapped_head_atoms) {
    					if (!new_query_atoms.contains(opa)) {
    						new_query_atoms.add(opa);
    						new_head = true;	// We found a new consequence, so we add it
    					}
    				}
    				
    				if (new_head) {
	    				OntologyConjunctiveQuery cq = new OntologyConjunctiveQuery(new_query_atoms, free_vars);
	    				Logger.debug("NEW CQ: " + cq);
	    				
	    				Map<OntologyConjunctiveQuery, Map<Term, Term>> newS = PolicyCons(policy, cq, new_sigma);
	    				
	    				for (var entry: newS.entrySet()) {
	    					S.putIfAbsent(entry.getKey(), entry.getValue());
	    				}
    				}			
    				
    			}
    		}
    	}
    	
    	return S;
    }
    
    // OntologyConjunctiveQuery
    private OntologyConjunctiveQuery CompleteCons(Set<EpistemicDependency> policy, OntologyConjunctiveQuery q, Map<Term, Term> sigma) throws URISyntaxException, PredicateArityException, TermTypeException {	//	, OntologyConjunctiveQuery q, HashMap<Term, Term> sigma) {
    	
    	/*
    	 * INPUT: 
    	 * 	- policy: set of epistemic dependencies
    	 *  - sigma: mapping from free vars of q to free vars of q, constants of q, and constants of the policy
    	 *  
    	 *  OUTPUT: 
    	 *   - conjunctive query (the query together with its policy consequences
    	 */
    	
    	if (sigma.isEmpty()) return q;
        
        
    	Set<OntologyPredicateAtom> original_atoms = q.getAllPredicateAtoms();
    	
    	/*
    	 * 	APPLY SIGMA TO THE QUERY
    	 */
    	
    	OntologyConjunctiveQuery sigmaQ = apply_sigma(q, sigma);
    	Set<OntologyPredicateAtom> sigmaQ_atoms = sigmaQ.getAllPredicateAtoms();
        
        
        List<Variable> free_vars = q.getFreeVariables();
        
        Set<OntologyPredicateAtom> C = new HashSet<>(sigmaQ_atoms);	
        Set<OntologyPredicateAtom> C_aux = new HashSet<>();
    	
        while (true) {
        	boolean new_head = false;	// to keep track when we add new consequences
        	
	    	for (EpistemicDependency ed: policy) {
	    		OntologyConjunctiveQuery body = ed.getBody();
	    		
	    		
	    		ArrayList<Variable> universally_quantified_vars = ed.getUniversallyQuantifiedVariables();
	    		
	    		Set<OntologyPredicateAtom> atoms = body.getAllPredicateAtoms();
	    		
	        	ArrayList<OntologyPredicateAtom> ED_atoms = new ArrayList<>();
	        	for (OntologyPredicateAtom a: atoms) {
	        		ED_atoms.add(a);        	
	        	}
	        	
	    
	        	ArrayList<HashMap<Term, Term>> simple_homos = simple_homomorphism(ED_atoms, C, universally_quantified_vars);
	        
	        	
	        	if (!simple_homos.isEmpty()) {
	        		
	        		
	        		OntologyConjunctiveQuery head = ed.getHead();
	        	
	        		
	        		for (Map<Term, Term> h: simple_homos) {
	        			OntologyConjunctiveQuery mapped_head = apply_sigma(head, h);
	        			Set<OntologyPredicateAtom> mapped_atoms_head = mapped_head.getAllPredicateAtoms();
	        			
	        			for (OntologyPredicateAtom a: mapped_atoms_head) {
	        				if (!C.contains(a)) {
	        					C.add(a);
	        					C_aux.add(a);
	        					new_head = true;
	        				}
	        			}
	        		}

	        	}
	    	}
	    	
	    	if (!new_head) {
	    		break;
	    	}
    		
    	}
        
        
        Set<OntologyPredicateAtom> new_atoms = new HashSet<>(original_atoms);
        new_atoms.addAll(C_aux);
        OntologyConjunctiveQuery cq = new OntologyConjunctiveQuery(new_atoms, free_vars);
        Logger.info("CQ with consequences: " + cq);
    	
    	return cq;
    }
    
    
    private ArrayList<HashMap<Term, Term>> simple_homomorphism(ArrayList<OntologyPredicateAtom> body_atoms, Set<OntologyPredicateAtom> query_atoms, List<Variable> universally_quantified_vars) {
    	/*
    	 * INPUT:
    	 * 		body_atoms: List of atoms occurring in the epistemic dependency
    	 * 		query_atoms: atoms occurring in the query
    	 * 
    	 * OUTPUT:
    	 * 		an array list of simple homomorphisms from body_atoms to query_atoms
    	 */
    	
    	ArrayList<HashMap<Term, Term>> h = new ArrayList<>(); 
    	
    	Result res = compute_homomorphisms(body_atoms, query_atoms, universally_quantified_vars);
    	
    	ArrayList<ArrayList<HashMap<Term, Term>>> homomorphisms = res.homomorphisms;
    	//ArrayList<Integer> indexes = res.indexes;
    	
    	
    	int l = homomorphisms.size();
    	
    	
    	// A simple homomorphism maps all the atoms of the body. If some of 
    	// these are not mapped, then we return the empty set
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
