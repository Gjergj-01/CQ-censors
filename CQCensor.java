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
import cqcensors.fol.DataConstant.DatatypeNoMatchException;

import org.semanticweb.owlapi.model.*;
import java.util.*;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.regex.Pattern;
import java.util.regex.Matcher; 

import static cqcensors.QueryChecker.loadEDPolicyFromJson;
import static cqcensors.util.OntologyUtils.loadOntology;
import static cqcensors.Increment.Increment_all;
import static cqcensors.Increment.Increment_all_non_zeros;
//import static cqcensors.Increment.printArray;

/**
 *
 * @author gjergj
 */
public class CQCensor {
    
    Configuration configuration; 
    String queryFilePath; 
    static OWLOntology tbox; 
    static Set<EpistemicDependency> policy; 
    private static String ONTOLOGY_IRI;
    
    public CQCensor(Configuration config) throws OWLOntologyCreationException, ParserException, Term.TermTypeException, IOException {
        configuration = config; 
        queryFilePath = config.prependInputPath(config.queryFilename);
        
        ONTOLOGY_IRI = config.ontologyIRI;
               
        // Load the policy from the JSON file 
        policy = loadEDPolicyFromJson(config.prependInputPath(config.policyFilename), 
                config.prependInputPath(config.ontologyFilename));
        
        
        ComputeClashQueries(policy);
        
        /*
        // Load OWL ontology
        tbox = loadOntology(config.prependInputPath(config.ontologyFilename));  → HERE it breaks
        System.out.println("I'm also here");
        
        // Check policy's acyclicity w.r.t. the TBox
        if (isAcyclicPolicy(policy, tbox)) {
            Logger.info("ACYCLIC POLICY OF SIZE: " + policy.size());
        }
        else {
            Logger.info("POLICY NOT ACYCLIC, EXITING ..."); // Maybe should raise an ERROR
        }
        System.out.println("Maybe even here here");
        */
        
    }
    
    private boolean isAcyclicPolicy(Set<EpistemicDependency> policy, OWLOntology tbox) throws IOException {
        DependencyGraph dg = new DependencyGraph(policy, tbox); 
        return dg.isPolicyAcyclic();
    }
   
    
    private Set<PredicateAtom> SPARQL_parser(String sparql) {
    	
        /*
            SPARQL parser 
            Takes in input a SPARQL query and returns its set of atoms. 
            Example.
            Given:
                SELECT ?x ?y
                WHERE {
                    ?x :R ?y .
                    ?y rdf:type Professor .
                    ?y a Person .
                }
            
            Returns: R(x,y), Professor(y), Person(y)
         
        */
    	
    	
        // Map<String, List<Tuple>> atoms = new HashMap<>();
    	Set<PredicateAtom> atoms = new HashSet<>();
        String membership_assertion = "rdf:type";
        String membership_assertion_shorten = "a";

        String BGP_regex = "(\\?\\w+|\\w+)\\s+(:?\\w+|rdf:type|a)\\s+(\\?\\w+|:?\\w+)\\s*\\.";

        Pattern pattern = Pattern.compile(BGP_regex, Pattern.DOTALL);

        Matcher matcher = pattern.matcher(sparql); 

        boolean found = false; 

        while (matcher.find()) {
            found = true;
            
            List<Term> terms = new ArrayList<>();

            String t1 = matcher.group(1); 
            String t2 = matcher.group(2); 
            String t3 = matcher.group(3);

            if (t2.equals(membership_assertion) || t2.equals(membership_assertion_shorten)) {
            	
            	// ?x a Person . , John rdf:type Person .
            	
            	if (t1.startsWith("?")) { // then t1 is a variable
            		
            		// Remove non alphanumeric characters in order to store just R(x,y) and not :R(?x, ?y)
                    t1 = t1.replaceAll("[^a-zA-Z0-9]", "");
                    t3 = t3.replaceAll("[^a-zA-Z0-9]", "");
                    
                    Variable v = new Variable(t1); 
                    terms.add(v);
                    
                    PredicateAtom atom = new PredicateAtom(t3, terms);
                    atoms.add(atom);
            		
            	}
            	
            	else { // t1 is a constant
            		
            		t1 = t1.replaceAll("[^a-zA-Z0-9]", "");
                    t3 = t3.replaceAll("[^a-zA-Z0-9]", "");
                    
                    try {
                    	DataConstant constant = new DataConstant(t1);
                    	terms.add(constant);
                    	PredicateAtom atom = new PredicateAtom(t3, terms);
                    	atoms.add(atom);
                    	
                    }catch (DatatypeNoMatchException e) {
                    	System.out.println("Type mismatch");
                    }
            		
            	}

                //Tuple tuple = new Tuple(t1);
                //atoms.computeIfAbsent(t3, k -> new ArrayList<>()).add(tuple);
             
            }
            else {
            	
            	if (t1.startsWith("?") && t3.startsWith("?")) {
            		// Both t1 and t2 are variables
            		
            		// Clean the strings
            		t1 = t1.replaceAll("[^a-zA-Z0-9]", "");
                    t2 = t2.replaceAll("[^a-zA-Z0-9]", "");
                    t3 = t3.replaceAll("[^a-zA-Z0-9]", "");
                    
                    Variable v1 = new Variable(t1); 
                    Variable v2 = new Variable(t3); 
                    
                    terms.add(v1); 
                    terms.add(v2);
                    
                    PredicateAtom atom = new PredicateAtom(t2, terms);
                    atoms.add(atom);
            		
            	}
            	
            	else if (t1.startsWith("?") && !t3.startsWith("?")) {
            		// t1 is a variable and t3 is a constant
            		
            		// Clean the strings
            		t1 = t1.replaceAll("[^a-zA-Z0-9]", "");
                    t2 = t2.replaceAll("[^a-zA-Z0-9]", "");
                    t3 = t3.replaceAll("[^a-zA-Z0-9]", "");
                    
                    Variable v1 = new Variable(t1); 
                    
                    try {
                    	DataConstant constant = new DataConstant(t3);
                    	terms.add(v1); 
                    	terms.add(constant);
                    	
                    	PredicateAtom atom = new PredicateAtom(t2, terms);
                    	atoms.add(atom);
                    	
                    } catch(DatatypeNoMatchException e) {
                    	System.out.println("Type mismatch");
                    }
            		
            	}
            	
            	else if (!t1.startsWith("?") && t3.startsWith("?")) {
            		// t1 is a constant and t3 is a variable
            		
            		// Clean the strings
            		t1 = t1.replaceAll("[^a-zA-Z0-9]", "");
                    t2 = t2.replaceAll("[^a-zA-Z0-9]", "");
                    t3 = t3.replaceAll("[^a-zA-Z0-9]", "");
                    
                    try {
                    	DataConstant constant = new DataConstant(t1);
                    	Variable v3 = new Variable(t3);
                    	terms.add(constant);
                    	terms.add(v3);
                    	
                    	PredicateAtom atom = new PredicateAtom(t2, terms);
                    	atoms.add(atom);
                    	
                    } catch(DatatypeNoMatchException e) {
                    	System.out.println("Type mismatch");
                    }
            		
            	}
            	
            	else { // Both t1 and t3 are constants
            		
            		// Clean the strings
            		t1 = t1.replaceAll("[^a-zA-Z0-9]", "");
                    t2 = t2.replaceAll("[^a-zA-Z0-9]", "");
                    t3 = t3.replaceAll("[^a-zA-Z0-9]", "");
            		
            		try {
            			DataConstant c1 = new DataConstant(t1);
            			DataConstant c2 = new DataConstant(t3);
            			
            			terms.add(c1); 
            			terms.add(c2);
            			
            			PredicateAtom atom = new PredicateAtom(t2, terms); 
            			atoms.add(atom);
            			
            		} catch(DatatypeNoMatchException e) {
            			System.out.println("Type mismatch");
            		}
            		
            	}

            }

        }

        if (!found) System.out.println("No match found!");
        
        return atoms;
           
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
    	
    	/*
    	 * indexes: an ArrayList to keep track of the indexes in body_atoms. 
    	 * We will use it to keep track of the atoms that we are considering for a given combination of homomorphism, 
    	 * precisely we store it's position (index) in the body of delta
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

    				
    				if (universally_quantified_vars.stream().anyMatch(v -> v.getName().equals(((Variable) b_t1).getName())) && q_t1 instanceof Variable) {
    				//if (universally_quantified_vars.contains(b_t1) && q_t1 instanceof Variable) {
    					// Can't map a free variable onto an existential variable
    					continue;
    				}
    				else if (b_t1 instanceof DataConstant && !(q_t1 instanceof DataConstant)) {
    					continue;
    				}
    				else if (b_t1 instanceof DataConstant && q_t1 instanceof DataConstant && !(b_t1.equals(q_t1))) { 
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
    			//System.out.println("Index: " + index);
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
    @SuppressWarnings("unchecked")
	public Set<Formula> ComputeClashQueries(Set<EpistemicDependency> policy) throws IOException{
        
        Set<Formula> res = new HashSet<>();
        
        // parse the query
        String sparql_query = "";
        try {
            sparql_query = Files.readString(Path.of(queryFilePath));
            
        } catch(IOException e) {
            System.out.println("File not found! " + e.getMessage());
        }
        
        // Retrieve the set of Atoms in the sparql query
        Set<PredicateAtom> sparql_query_atoms = SPARQL_parser(sparql_query);
        System.out.println("*** SPARQL query atoms ***");
        System.out.println(sparql_query_atoms);
        
        for (EpistemicDependency ed: policy) {
        	OntologyConjunctiveQuery body = ed.getBody();
        	
        	System.out.println("*** ED body ***");
        	System.out.println(body);
        	
        	
        	ArrayList<Variable> universally_quantified_vars = ed.getUniversallyQuantifiedVariables();
        	System.out.println("*** Free variables ***");
        	System.out.println(universally_quantified_vars);
        	
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
        	System.out.println("*** Indexes ***");
        	System.out.println(indexes);
        	
        	System.out.println("***** Printing Homomorphisms ******");
        	
        	for (ArrayList<HashMap<Term,Term>> a: homomorphisms) {
        		System.out.println(a);
        	}
        	
        	int l = homomorphisms.size();
        	if (l == 0) continue; // No homomorphisms for this delta
        	
        	// We compute K, an array storing the counter of the number of homomorphisms 
        	// found for each atom (except those for which the count is zero.
        	ArrayList<Integer> K = new ArrayList<>();
        	
        	for (ArrayList<HashMap<Term, Term>> a: homomorphisms) {
        		K.add(a.size());
        	}
        	System.out.println("*** Printing K ***");
        	System.out.println(K);
        	
        	// Initialization of the matrix (or hashmap) M 
        	
        	ArrayList<Integer> A = new ArrayList<>();
        	for (int j = 0; j < l; j++) {
        		A.add(0);
        	}
        	HashMap<ArrayList<Integer>, Integer> M = initialize_map(A, K, l);
        	
        	
        	System.out.println("*** HashMap M ***");
        	for (var entry : M.entrySet()) {
                ArrayList<Integer> keyStr = entry.getKey();
                Integer value = entry.getValue();
                System.out.print(keyStr + ":" + value + "  ");
            }
        	System.out.println();
        	
        	
        	/*
        	 * EXPLORE: Next we explore all the possible combinations of homomorphisms to keep
        	 * 			just the admissible ones.
        	 */
        	ArrayList<Integer> A_init = new ArrayList<>();
        	// Initialize Ainit with all 1s
        	for (int i = 0; i < l; i++) {
        		A_init.add(1); 
        	}
        	
        	ArrayList<Integer> A1 = (ArrayList<Integer>) A_init.clone();
        	ArrayList<Integer> A2 = new ArrayList<>();
        	
        	
        	do {
	        	M = CheckClash(ED_atoms, homomorphisms, A1, M, l, indexes);
	        	A2 = (ArrayList<Integer>) A1.clone(); 
	        	A1 = Increment_all_non_zeros(A1, K);
        	} while (!A1.equals(A2));
        	
        	
        	System.out.println("*** HashMap M after CHECK CLASH ***");
        	for (var entry : M.entrySet()) {
                ArrayList<Integer> keyStr = entry.getKey();
                Integer value = entry.getValue();
                System.out.print(keyStr + ":" + value + "  ");
            }
        	System.out.println();
        
        }
        
        // TODO: Generate Conjunctive Queries
        
        
        
        return res;
        
    }
    
    
    private HashMap<ArrayList<Integer>, Integer> initialize_map(ArrayList<Integer> A, ArrayList<Integer> K, int l) {
    	
    	/*
    	 * Auxiliary method to initialize the Map M containing the possible combinations of homomorphisms
    	 */
    	
    	HashMap<ArrayList<Integer>, Integer> M = new HashMap<ArrayList<Integer>, Integer>(); 
    	
    	M.put(A, 0); // M[0,...,0] = 0 since it corresponds to the body
    	
    	ArrayList<Integer> A1 = (ArrayList<Integer>) A.clone();
    	ArrayList<Integer> A2 = new ArrayList<>();
    	
    	// Initialize A2 with -1s
    	for (int i = 0; i < l; i++) {
    		A2.add(-1);
    	}
    	
    	while (!A1.equals(A2)) {
    		A2 = (ArrayList<Integer>) A1.clone();
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
    	//HashMap<int[], Integer> M1 = (HashMap<int[], Integer>) M.clone();
    	
    	System.out.println("*** A ***: " + A);
    	
    	ArrayList<HashMap<Term, Term>> sigma = new ArrayList<HashMap<Term, Term>>();
    	
    	// Initialize the array B
    	// B = {alpha_i | A[i] > 0}
    	
    	int num_atoms = ED_atoms.size();
    	
    	ArrayList<OntologyPredicateAtom> B = new ArrayList<>();
    	
    	for (int i = 0; i < num_atoms; i++) {
    		if (!I.contains(i)) {
    			// I contains only the indexes of the atoms for which
    			// we found at least one homo
    			B.add(ED_atoms.get(i));
    		}
    	}
    	
    	for (int i = 0; i < l; i++) {
    		if (A.get(i) == 0) {
    			B.add(ED_atoms.get(I.get(i)));
    		}
    	}
    	
    	for (int i = 0; i < l; i++) {
    		if (A.get(i) > 0) {
    			sigma.add(H.get(i).get(A.get(i)-1));	// H[1][A[1] \cup ... \cup H[l]A[l]
    		}
    	}
    	
    	System.out.println("*** Printing B ***");
    	System.out.println(B);
    	
    	/*
    	 * CHECK ADIMISSIBILITY
    	 * Sigma is admissible if it passes the following two checks:
    	 *     -1: it is a homomorphism
    	 *     -2: if x is a variable occurring in the domain of sigma and sigma(x) is a variable. 
    	 *         then x does not appear in Atoms(ED) minus dom(sigma).
    	 */
    	
    	boolean adm = true;
    	
    	for (HashMap<Term, Term> h1: sigma) {
    		for (var entry: h1.entrySet()) {
    			for (HashMap<Term, Term> h2: sigma) {
    				if (!h1.equals(h2)) {
    					for (var entry2: h2.entrySet()) {
    						if (entry.getKey().equals(entry2.getKey()) && !entry.getValue().equals(entry2.getValue())) { 
    							// This is not even a homomorphism, the same variable is mapped to two different values
    							adm = false;
    							break;
    						}
    					}
    				}
    				if (!adm) break;
    			}
    			if (!adm) break;
    			
    			// Check the second condition
    			if (entry.getValue() instanceof Variable) {
    				Variable v = (Variable) entry.getKey();
    				for (OntologyPredicateAtom oa: B) {
    					if (oa.getFreeVariables().contains(v)) {
    						// Condition 2 is not satisfied
    						System.out.println("Condition 2 is not sat");
    						adm = false;
    						break;
    						
    					}
    				}
    				
    			}
    		}
    		if (!adm) {
    			M.replace(A, 0);	// Set the entry M[A] = 0;
    			break;
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
    		return M;
    	}
    	
    	for (int i = 0; i < l; i++) {
    		if (A.get(i) != 0) {
    			@SuppressWarnings("unchecked")
				ArrayList<Integer> A1 = (ArrayList<Integer>) A.clone();
    			A1.set(i, 0);
    			System.out.println("Enetering");
    			if ((int) M.get(A1) != 0) {
    				System.out.println("Recursively calling CheckClash");
    				M = CheckClash(ED_atoms, H, A1, M, l, I);
    			}
    		}
    	}
    	
 
    	
    	System.out.println("*** Printing SIGMA ***");
    	System.out.println(sigma);
    	
    	
    	return M;
    	
    }
    
    
    
}
