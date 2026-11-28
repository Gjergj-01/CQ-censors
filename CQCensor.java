/*
 * Click nbfs://nbhost/SystemFileSystem/Templates/Licenses/license-default.txt to change this license
 * Click nbfs://nbhost/SystemFileSystem/Templates/Classes/Class.java to edit this template
 */
package cqcensors;

import cqcensors.fol.*;
//import cqcensors.fol.DataConstant.DatatypeNoMatchException;
import cqcensors.fol.PredicateAtom.PredicateArityException;
import cqcensors.policy.EpistemicDependency;
import cqcensors.policy.DependencyGraph;
import cqcensors.policy.OntologyConjunctiveQuery;
import cqcensors.parser.ParserException;
import cqcensors.fol.Term.TermTypeException;
import cqcensors.db.*;
import cqcensors.db.SQLCompiler.SQLificationException;
import cqcensors.db.SQLConnection.DriverNotFoundException;

import java.sql.*;

//import cqcensors.db.
import java.net.URISyntaxException;

import org.semanticweb.owlapi.model.*;
import java.util.*;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
//import java.nio.file.Paths;


import java.util.regex.Pattern;
import java.util.regex.Matcher;

//import cqcensors.fol.OntologyPredicateAtom.Type;


import static cqcensors.QueryChecker.loadEDPolicyFromJson;
import static cqcensors.QueryChecker.rewriteEDPolicyWrtTbox;
import static cqcensors.util.OntologyUtils.loadOntology;
import static cqcensors.Increment.Increment_all;
import static cqcensors.Increment.Increment_all_non_zeros;
import static cqcensors.SPARQLParser.SPARQL_parser;
import static cqcensors.SPARQLParser.getDistinguishedVars;
import static cqcensors.policy.EpistemicDependency.IND_AUX_PRED_NAME;
import static cqcensors.fol.MostGeneralUnifier.findMGU;




public class CQCensor {
    
    Configuration configuration; 
    String queryFilePath; 
    String userQuery_sparql;
    static OWLOntology tbox; 
    static Set<EpistemicDependency> policy; 
    static Set<EpistemicDependency> policyExpWrtTBox;	// ← policy expanded w.r.t. the TBox
    static Set<EpistemicDependency> policyExp; 			// ← policy expanded w.r.t. TBox and itself
    private static String ONTOLOGY_IRI;
    
    public CQCensor(Configuration config) throws OWLOntologyCreationException, ParserException, Term.TermTypeException, IOException, PredicateAtom.PredicateArityException, URISyntaxException, SQLificationException {
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
        
        // Read the query
        userQuery_sparql = Files.readString(Path.of(queryFilePath));
        
        /*
         * POLICY EXPANSION
         */
        
        
        //System.out.println("Expanding policy w.r.t. TBox");
        policyExpWrtTBox = rewriteEDPolicyWrtTbox(policy, tbox);
        // Logger.info("Policy Expanded w.r.t. TBox: " + expandedwrtTBox);
        
        
        //System.out.println("Expanding policy w.r.t. TBOX and itself");
        policyExp = expandAcyclicPolicy(policy, tbox);
        
        
        /*
         * POLICY CONSEQUENCES TESTS
         */
         
        //System.out.println("\n");
        
        Map<Term, Term> sigma = new HashMap<>();
        
        Variable v1 = new Variable("x");
        Variable v2 = new Variable("y");
        Variable v3 = new Variable("w");
        ObjectConstant c1 = new ObjectConstant("c1");
        ObjectConstant c2 = new ObjectConstant("c2");
 
        
        
        List<Term> terms1 = new ArrayList<>(); 
        terms1.add(v1);
        terms1.add(v2);
        
        List<Term> terms2 = new ArrayList<>(); 
        terms2.add(v2);
        //terms2.add(c);
        terms2.add(v3);
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
        free_vars.add(v3);
        
        OntologyConjunctiveQuery q = new OntologyConjunctiveQuery(atoms, free_vars);
        
        //Logger.info("Ontology CQ: " + q);
        
        //List<Map<Term, Term>> maps = new ArrayList<>();
        //maps = computePrecondition(free_vars, constants, sigma);
        
        
        //Logger.info("Unidirectional mappings \n: " + maps);
        
        //Map<OntologyConjunctiveQuery, Map<Term, Term>> S = PolicyCons(policyExpWrtTBox, q, sigma);
        
        //for (var entry: S.entrySet()) {
        //	System.out.println(entry.getKey() + ": " + entry.getValue());
        //}
        //Logger.info("S: " + S);
        
        //CompleteCons(policyExpWrtTBox, sigma);
        
        //ComputeClashQueries(policyExp);
        
        
        
        
        /*
         * Atoms equality tests
         */
        
        
        List<Term> atom1_terms = new ArrayList<>();
        atom1_terms.add(v1);
        atom1_terms.add(v2);
        
        List<Term> atom2_terms = new ArrayList<>();
        atom2_terms.add(v1);
        atom2_terms.add(v2);
        
       
        
        OntologyPredicateAtom atom1 = new OntologyPredicateAtom("C", atom1_terms);
        OntologyPredicateAtom atom2 = new OntologyPredicateAtom("C", atom2_terms);
        
        //Logger.debug("Atom1: " + atom1 + " Atom2: " + atom2);
        
       // Logger.info("Same atoms: " + same_atom(atom1, atom2));
        
        
        
        //Set<OntologyConjunctiveQuery> rewrittenQuery = TreeWitnessClient.rewriteQuery(userQuery_sparql, tbox, true);
        
        //Logger.info(rewrittenQuery);
        
        /*
         * BCQ rewriting
         */
        
        List<Term> terms = new ArrayList<>(); 
        terms.add(v1);
        OntologyPredicateAtom atom = new OntologyPredicateAtom("Patient", terms);
        List<OntologyPredicateAtom> BCQ_atoms = new ArrayList<>();
        BCQ_atoms.add(atom);
        OntologyConjunctiveQuery ocq = new OntologyConjunctiveQuery(BCQ_atoms,  new ArrayList<Variable>());
        
        ArrayList<Variable> ExistentialVars = ocq.getQuantifiedVariables();
        //Logger.info("Existential vars: " + ExistentialVars);
        
        //Formula f = new Exist((Formula) ocq.getBody(), ExistentialVars);
        
        //Logger.debug("Formula: " + f);
        
        //Logger.debug("BCQ: " + ocq);
        /*
        String sparql = ocq.toSparql();
        String formatted_sparql = format_query(sparql);
        Logger.debug(formatted_sparql);
        */
        
        //Set<OntologyConjunctiveQuery> rewrittenQuery = TreeWitnessClient.rewriteQuery(formatted_sparql, tbox, true);
        
        /*
         * phi_pc test
         */
        
        List<Variable> freeVars = new ArrayList<Variable>();
        freeVars.add(v1);
        OntologyConjunctiveQuery CQ = new OntologyConjunctiveQuery(BCQ_atoms, freeVars);
        
        //Logger.debug("CQ: " + CQ);
        
        // Disjunction d = phi_pc(CQ);
        
        //Logger.info("phi_pc: " + d);
        
        List<Variable> vars = new ArrayList<Variable>();
        
        vars.add(v1); 
        vars.add(v2);
        
        OntologyPredicateAtom AND = new OntologyPredicateAtom("clinicalData", vars);
        List<OntologyPredicateAtom> and_atoms = new ArrayList<OntologyPredicateAtom>();
        and_atoms.add(atom);
        and_atoms.add(AND);
        
        
        List<Variable> AND_freeVars = new ArrayList<>();
        AND_freeVars.add(v1);
        
        OntologyConjunctiveQuery AND_cq = new OntologyConjunctiveQuery(and_atoms, AND_freeVars);
        
        //Logger.info("AND_cq: " + AND_cq + " Free vars: " + AND_cq.getFreeVariables());
        
        //Disjunction d2 = phi_pc(AND_cq);
        
        //Logger.info("phi_pc2: " + d2);
        
        
        /*
         * Clash tests
         */
        
        // v1 → x, v2 → y, v3 → w
        
        /*
        List<Term> A_terms = new ArrayList<>();
        A_terms.add(v3);
        OntologyPredicateAtom A = new OntologyPredicateAtom("A", A_terms);
        Set<OntologyPredicateAtom> cq_atoms = new HashSet<>();
        cq_atoms.add(A);
        List<Variable> cq_freeVars = new ArrayList<>();
        cq_freeVars.add(v3);
        OntologyConjunctiveQuery cq = new OntologyConjunctiveQuery(cq_atoms, cq_freeVars);
        
        Logger.info("CQ: " + cq);
        
        
        List<Term> R_terms = new ArrayList<>();
        R_terms.add(v3);
        R_terms.add(v2);
        OntologyPredicateAtom R = new OntologyPredicateAtom("R", R_terms);
        Set<OntologyPredicateAtom> clash_atoms = new HashSet<>();
        clash_atoms.add(R);
        List<Variable> clash_freeVars = new ArrayList<>();
        clash_freeVars.add(v3);
        clash_freeVars.add(v2);
        OntologyConjunctiveQuery candidate_clash = new OntologyConjunctiveQuery(clash_atoms, clash_freeVars);
        
        Logger.info("clash: " + candidate_clash);
        
        String query = cq.toSparql();
        String sparql_query = format_query(query);
        
        Logger.debug("SPARQL query: " + sparql_query);
        
        Clash(candidate_clash, sparql_query);
        
        */
        
        
        
        /*
         * Perfect Reformulation tests
         */
        
        
        //rewrite(q);
        
        
        /*
         * SQL tests
         */
        /*
        try {
			sql_execution();
		} catch (SQLificationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (TermTypeException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (URISyntaxException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (PredicateArityException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		*/
        
        /*
        System.out.println("Query: " + q);
        try {
			sql_exec_OCQ(q);
		} catch (DriverNotFoundException | PredicateArityException | TermTypeException | URISyntaxException
				| SQLificationException | SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		*/
        
        
        /*
         * COMPLETE TEST
         */
        
        Set<OntologyConjunctiveQuery> Q = ComputeClashQueries(this.policyExp);
        
        Conjunction scentailedFormula = SC_entailed(Q);
        
        Logger.info("***** SC-Entailed ***** \n" + scentailedFormula);
        
        
        try {
			sql_exec_OCQ(scentailedFormula);
		} catch (DriverNotFoundException | PredicateArityException | TermTypeException | URISyntaxException
				| SQLificationException | SQLException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
        
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
    
    public Result compute_homomorphisms(ArrayList<OntologyPredicateAtom> body_atoms, Set<OntologyPredicateAtom> query_atoms, List<Variable> universally_quantified_vars, 
    									List<Variable> query_free_vars) {
    	ArrayList<ArrayList<HashMap<Term, Term>>> H = new ArrayList<ArrayList<HashMap<Term, Term>>>();
    	
    	/* INPUT:
    	 * 	body_atoms: List of atoms occurring in the body of the considered epistemic dependency
    	 * 	query_atoms: atoms occurring in the query
    	 * 	universally_quantified_vars: universally quantified variables in the epistemic dependency
    	 * 	query_free_vars: universally_quantified_free vars (only for computing policy consequences). The query posed to the knowledge base is a BCQ
    	 * 	
    	 * OUTPUT:
    	 * 	indexes: an ArrayList to keep track of the indexes in body_atoms. 
    	 * 		We will use it to keep track of the atoms that we are considering for a given combination of homomorphism, 
    	 * 		precisely we store it's position (index) in the body of delta
    	 * 	homomorphisms: the homomorphisms found for each atom in body delta
    	 */
    	ArrayList<Integer> indexes = new ArrayList<>(); 
    	
    	
    	if (query_free_vars.isEmpty()) {
    		int index = 0;
	    	for (OntologyPredicateAtom b_a: body_atoms) {
	    		ArrayList<HashMap<Term, Term>> homomorphisms = new ArrayList<HashMap<Term, Term>>();
	    		for (OntologyPredicateAtom q_a: query_atoms) {
	    			if (b_a.getPredicateName().equals(q_a.getPredicateName()) && b_a.getArity() == q_a.getArity()) {
	    				HashMap<Term, Term> h = new HashMap<>();
	    				
	    				Term b_t1 = b_a.getTerm(0);		// term 1 of the body's atom
	    				Term q_t1 = q_a.getTerm(0);		// term 1 of the query's atom
	
	    				
	    				if (q_t1 instanceof Variable && universally_quantified_vars.stream().anyMatch(v -> v.getName().equals(((Variable) b_t1).getName()))) {
	    				//if (universally_quantified_vars.contains(b_t1) && q_t1 instanceof Variable) {
	    					// Can't map a free variable onto an existential variable
	    					continue;
	    				}
	    				else if (b_t1 instanceof ObjectConstant && !(q_t1 instanceof ObjectConstant)) {
	    					// a homomorphisms preservers the constants
	    					continue;
	    				}
	    				else if (b_t1 instanceof ObjectConstant && q_t1 instanceof ObjectConstant && !(b_t1.equals(q_t1))) { 
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
	    					else if (b_t2 instanceof ObjectConstant && !(q_t2 instanceof ObjectConstant)) {
	        					continue;
	        				}
	        				else if (b_t2 instanceof ObjectConstant && q_t2 instanceof ObjectConstant && !(b_t2.equals(q_t2))) {
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
    	}
    	else {
    		int index = 0;
	    	for (OntologyPredicateAtom b_a: body_atoms) {
	    		ArrayList<HashMap<Term, Term>> homomorphisms = new ArrayList<HashMap<Term, Term>>();
	    		for (OntologyPredicateAtom q_a: query_atoms) {
	    			if (b_a.getPredicateName().equals(q_a.getPredicateName()) && b_a.getArity() == q_a.getArity()) {
	    				HashMap<Term, Term> h = new HashMap<>();
	    				
	    				Term b_t1 = b_a.getTerm(0);		// term 1 of the body's atom
	    				Term q_t1 = q_a.getTerm(0);		// term 1 of the query's atom
	
	    				
	    				if (q_t1 instanceof Variable && universally_quantified_vars.stream().anyMatch(v -> v.getName().equals(((Variable) b_t1).getName())) 
	    						&& !(query_free_vars.stream().anyMatch(v -> v.getName().equals(((Variable) q_t1).getName())))) {
	    				//if (universally_quantified_vars.contains(b_t1) && q_t1 instanceof Variable) {
	    					// Can't map a free variable onto an existential variable
	    					
	    					
	    					Logger.warn("Query free vars: " + query_free_vars);
	    					Logger.warn("Query term t1: " + q_t1);
	    					Logger.error("Query free vars contains t1: " + query_free_vars.contains(((Variable) q_t1).getName()));
	    					Logger.error(((Variable) q_t1).getQuery());
	    					Logger.error(query_free_vars.get(0).getQuery());
	    					continue;
	    				}
	    				
	    				else if (b_t1 instanceof ObjectConstant && !(q_t1 instanceof ObjectConstant)) {
	    					// a homomorphisms preservers the constants
	    					continue;
	    				}
	    				else if (b_t1 instanceof ObjectConstant && q_t1 instanceof ObjectConstant && !(b_t1.equals(q_t1))) { 
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
	    					
	    					if (universally_quantified_vars.stream().anyMatch(v -> v.getName().equals(((Variable) b_t2).getName())) && q_t2 instanceof Variable  
	    							&& !(query_free_vars.stream().anyMatch(v -> v.getName().equals(((Variable) q_t2).getName())))) {
	    						continue;
	    					}
	    					else if (b_t2 instanceof ObjectConstant && !(q_t2 instanceof ObjectConstant)) {
	        					continue;
	        				}
	        				else if (b_t2 instanceof ObjectConstant && q_t2 instanceof ObjectConstant && !(b_t2.equals(q_t2))) {
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
      
        //String sparql_query = Files.readString(Path.of(queryFilePath));
        //Logger.info("Read SARQL_query: \n" + sparql_query);
        
        // Retrieve the set of Atoms in the sparql query
        Set<OntologyPredicateAtom> sparql_query_atoms = SPARQL_parser(this.userQuery_sparql);
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
        	List<Variable> distinguishedVars = getDistinguishedVars(this.userQuery_sparql);
        	//List<Variable> query_free_vars = new ArrayList<>();		// The query posed to the KB is a BCQ so it has no free vars
        	Result ris = compute_homomorphisms(ED_atoms, sparql_query_atoms, universally_quantified_vars, distinguishedVars);
        	
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
                							if (free_vars.contains(x) && e.getValue() instanceof Variable) {
                								// the variable has been mapped to a free variable
                								free_vars.remove(x);
                								free_vars.add((Variable) e.getValue());
                							}
                							else if (free_vars.contains(x)) { 
                								// the variable has been mapped to a constant, 
                								// simply remove it from freeVars
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
    	 *     -2: if x is a EXISTENTIAL variable occurring in the domain of sigma and sigma(x) is a variable. 
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
	    				
	    				// If the atom contains the variable v and v is not a free variable
	    				// then v is an existential var and the homomorphism is not admissible
	    				if (oa.getVariables().contains(v) && !oa.getFreeVariables().contains(v)) {
	    					
	    					adm = false;
	    					break;
	    				}
	    				/*
	    				if (oa.getFreeVariables().contains(v)) {		// → NEED TO RETURN ON THIS!! WHY FREE VARIABLES?
	    					adm = false; 
	    					break;
	    				}
	    				*/
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
    	
    	System.out.println("\n");
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
    	
    	// Compute the set of preconditions for computing a simple homomorphism
    	List<Map<Term, Term>> preconditions = computePrecondition(sigma_q_free_vars, cons);
    	
    	if (preconditions.get(0).isEmpty()) return S;
    	
    	Logger.info("Preconditions: " + preconditions);
    	
    	for (Map<Term, Term> p: preconditions) {
    		Logger.error("Considering Precondition: " + p);
    		
    		// Apply precondition p to the atoms of the mapped query, i.e. sigma(q)
			
			OntologyConjunctiveQuery p_q = apply_sigma(sigma_q, p);
			Set<OntologyPredicateAtom> mapped_atoms = p_q.getAllPredicateAtoms();
			ArrayList<Variable> p_q_free_vars = p_q.getFreeVariables();
			Logger.debug("h'(q):" + p_q);
			
			
    		for (EpistemicDependency ed: policy) {
    			 			
    			// Compute the simple homomorphisms from body(delta) to p(q)
    			
    			OntologyConjunctiveQuery body = ed.getBody();
    			Set<OntologyPredicateAtom> ED_body_atoms = body.getAllPredicateAtoms();
    			ArrayList<OntologyPredicateAtom> body_atoms = new ArrayList<>();
            	for (OntologyPredicateAtom a: ED_body_atoms) {
            		body_atoms.add(a);        	
            	}
            	
    			ArrayList<Variable> body_free_vars = ed.getUniversallyQuantifiedVariables();

    			// Finally compute the simple homomorphisms
    			ArrayList<HashMap<Term, Term>> simple_homos = simple_homomorphism(body_atoms, mapped_atoms, body_free_vars, p_q_free_vars);
    			
    			//Logger.debug("body_atoms: " + body_atoms + " Mapped atoms: " + mapped_atoms);
    			
    			if (simple_homos.isEmpty()) continue;	// If no simple homomorphism was found, then continue
    			
    			Logger.info("\nFound simple homos: " + simple_homos);
    			//Logger.warn("Sigma: " + sigma);
    			
    			/*
    			 *	If we found a simple homomorphisms, then we check if we can build a new significant mapping.
    			 *	Again, we want to avoid the following kind of mappings:
    			 *		1. {x → y}; then avoids putting y → c
    			 *		2. {y → c}; then it avoids putting x → y
    			 */
    		
    			boolean relevant = true;
    			for (var entry: p.entrySet()) {
    				if (sigma.containsValue(entry.getKey()) || sigma.containsKey(entry.getValue())) {
    					relevant = false;
    					break;
    				}
    			}
    			if (!relevant) continue;
    			
    			
    			Logger.error("Current simga: " + sigma);
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
    	
    	Logger.info("Query: " + q + " Sigma: " + sigma);
    	
    	// if (sigma.isEmpty()) return q;
        
        
    	Set<OntologyPredicateAtom> original_atoms = q.getAllPredicateAtoms();
    	
    	/*
    	 * 	APPLY SIGMA TO THE QUERY
    	 */
    	
    	OntologyConjunctiveQuery sigmaQ = apply_sigma(q, sigma);
    	Set<OntologyPredicateAtom> sigmaQ_atoms = sigmaQ.getAllPredicateAtoms();
    	List<Variable> sigmaQ_free_vars = sigmaQ.getFreeVariables();
        
        
        List<Variable> free_vars = q.getFreeVariables();
        
        Set<OntologyPredicateAtom> C = new HashSet<>(sigmaQ_atoms);	
        Set<OntologyPredicateAtom> C_aux = new HashSet<>();
    	
        while (true) {
        	boolean new_head = false;	// to keep track when we add new consequences
        	
	    	for (EpistemicDependency ed: policy) {
	    		OntologyConjunctiveQuery body = ed.getBody();
	    		
	    		//if (ed.isDenial()) {
				//	Logger.warn("HEAD: " + ed.getHead());
				//}
	    		
	    		ArrayList<Variable> universally_quantified_vars = ed.getUniversallyQuantifiedVariables();
	    		
	    		Set<OntologyPredicateAtom> atoms = body.getAllPredicateAtoms();
	    		
	        	ArrayList<OntologyPredicateAtom> ED_atoms = new ArrayList<>();	// We need an array (not set) of atoms
	        	for (OntologyPredicateAtom a: atoms) {
	        		ED_atoms.add(a);        	
	        	}
	        	
	    
	        	// compute the simple homomorphisms from the body of the ED to C 
	        	ArrayList<HashMap<Term, Term>> simple_homos = simple_homomorphism(ED_atoms, C, universally_quantified_vars, sigmaQ_free_vars);
	        
	        	
	        	if (!simple_homos.isEmpty()) {
	        		
	        		
	        		OntologyConjunctiveQuery head = ed.getHead();
	        		
	        		if (ed.isDenial()) {
	        			// if we found a denial, we simply return the empty head
	        			
	        			return head;
	        		}
	        	
	        		
	        		for (Map<Term, Term> h: simple_homos) {
	        			OntologyConjunctiveQuery mapped_head = apply_sigma(head, h);
	        			Set<OntologyPredicateAtom> mapped_atoms_head = mapped_head.getAllPredicateAtoms();
	        			
	        			
	        			// Check if we can add a new Immediate Consequence
	        			for (OntologyPredicateAtom head_atom: mapped_atoms_head) {
	        				boolean found = false;
	        				for (OntologyPredicateAtom a: C) {
	        					
	        					if (same_atom(head_atom, a)) {
	        						found = true; 
	        						break;
	        					}
	        				}
	        				
	        				if (!found) {
	        					
	        					C.add(head_atom);
	        					C_aux.add(head_atom);
	        					//Logger.error("Adding head atom: " + head_atom);
	        					
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
    
    
    
    private boolean same_atom(OntologyPredicateAtom a1, OntologyPredicateAtom a2) {
    	
    	
    	
    	if (!(a1.getArity() == a2.getArity())) {
    		return false;
    	}
    	else if (!(a1.getPredicateName().equals(a2.getPredicateName()))) {
    		return false;
    	}
    	
    	for (int i = 0; i < a1.getTerms().size(); i++) {
    		// Get terms
	    	Term at1 = a1.getTerm(i); 
	    	Term at2 = a2.getTerm(i); 
	    	
	    	if (!(at1.getClass().equals(at2.getClass()))) {
	    		return false;
	    	}
	    	
	    	if (at1 instanceof Variable && at2 instanceof Variable) {
	    		if (!((Variable) at1).getName().equals(((Variable) at2).getName())) {
	    			return false;
	    		}
	    	}
	    	// the terms are object constants
	    	else if (!(at1.equals(at2))) {
	    		return false;
	    	}  	
    	}
    	
    	
    	return true;
    }
    
    
    private ArrayList<HashMap<Term, Term>> simple_homomorphism(ArrayList<OntologyPredicateAtom> body_atoms, Set<OntologyPredicateAtom> query_atoms, 
    															List<Variable> universally_quantified_vars, List<Variable> query_free_vars) {
    	/*
    	 * INPUT:
    	 * 		body_atoms: List of atoms occurring in the epistemic dependency
    	 * 		query_atoms: atoms occurring in the query
    	 * 
    	 * OUTPUT:
    	 * 		an array list of simple homomorphisms from body_atoms to query_atoms
    	 */
    	
    	ArrayList<HashMap<Term, Term>> h = new ArrayList<>(); 
    	
    	Result res = compute_homomorphisms(body_atoms, query_atoms, universally_quantified_vars, query_free_vars);
    	
    	ArrayList<ArrayList<HashMap<Term, Term>>> homomorphisms = res.homomorphisms;
    	//Logger.error("Found homos: " + homomorphisms);
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
    
    
    
    
    /*
     * 		SC-entailment methods
     */
    
    
    
    public Disjunction phi_pc(OntologyConjunctiveQuery q) throws URISyntaxException, PredicateArityException, TermTypeException {
    	
    	/*
    	 * Input:
    	 * 		OntologyConjunctiveQuery
    	 * 
    	 *  The method computes the policy consequences of the query, 
    	 *  rewrites the conjunction of the query and her policy consequences, 
    	 *  returns the Disjunction of the rewriting
    	 */
    	
    	Disjunction disj = new Disjunction();
    	Map<Term, Term> empty_sigma  = new HashMap<Term, Term>();
    	// compute policy consequences
    	
    	/*
    	 * NOTE: in the current implementation CompleteCons returns the conjunction of the query and its consequences
    	 */
    	OntologyConjunctiveQuery query_with_cons = CompleteCons(this.policyExpWrtTBox, q, empty_sigma);
    		
    	if (query_with_cons.containsOnlyFalse()) {
    		disj.add(new False());
    		return disj;
    	}
    	
    	// convert query to sparql
    	String sparql = query_with_cons.toSparql();	
    	
    	
    	// Format the query for the rewriting algorithm
    	String formatted_query = format_query(sparql);
    
    	//Logger.debug("SPARQL query: " + sparql);
    	
    	// rewrite query
    	Set<OntologyConjunctiveQuery> rewrittenQuery = TreeWitnessClient.rewriteQuery(formatted_query, tbox, true);
    	
    	
    	// Build the disjunction of the rewritings
    	
    	for (OntologyConjunctiveQuery ocq: rewrittenQuery) {
    		ocq.explicitNondistinguishedNonsharedVariables();
    		//Conjunction innerConjunction = new Conjunction();
    		ArrayList<Variable> existentialVars = ocq.getQuantifiedVariables();
    		Conjunction cq = ocq.getBody();
    		
    		if (!existentialVars.isEmpty()) {
    			disj.add(new Exist((Formula) cq, existentialVars));
    		} else {
    			disj.add(cq);
    		}
    	}
    	
    	
    	return disj;
    	
    }
    
    
    
    public Negation Clash(OntologyConjunctiveQuery candidate_clash, Set<OntologyPredicateAtom> userQuery_atoms, List<Variable> distinguishedVars) throws URISyntaxException, PredicateArityException, TermTypeException {
    	/*
    	 * 	Input:
    	 * 		- candidate_clash: CQ q that is a potential clash for the user query in the CQE instance
    	 * 		- userQuery: the (sparql) query posed to the Knowledge Base
    	 * 
    	 *  Output:
    	 *  	- Clash formula
    	 */
    	
    	
    	/*
    	 * 	Next we build the conjunction (AND) of the original query and the candidate clash query
    	 */
    	
    	Set<OntologyPredicateAtom> candidate_clash_atoms = candidate_clash.getOntologyPredicateAtoms(); 
    	Set<OntologyPredicateAtom> AND_atoms = new HashSet<>(candidate_clash_atoms);
    	AND_atoms.addAll(userQuery_atoms);
    	
    	List<Variable> candidate_clash_freeVars = candidate_clash.getFreeVariables();
    	List<Variable> AND_freeVars = new ArrayList<>(distinguishedVars);
    	for (Variable v: candidate_clash_freeVars) {
    		if (!AND_freeVars.contains(v)) {
    			AND_freeVars.add(v);
    		}
    	}
    	
    	OntologyConjunctiveQuery AND = new OntologyConjunctiveQuery(AND_atoms, AND_freeVars);
    	
    	Logger.debug("AND: " + AND);
    	
    	// We build the two phi_pcs 
    	// - One for the candidate clash query
    	// - the other for the conjunction of the candidate clash and the user query
    	Disjunction phi_pc1 = phi_pc(candidate_clash);
    	Disjunction phi_pc2 = phi_pc(AND);
    	
    	ArrayList<Variable> existentialVars = new ArrayList<Variable>();
    	
    	// In the clash query, all the free variables (except for the distinguished ones in the user query) 
    	// need to be quantified existentially
    	for (Variable v: candidate_clash_freeVars) {
    		if (!distinguishedVars.contains(v)) {
    			existentialVars.add(v);
    		}
    	}
    	
    	Conjunction innerConjunction = new Conjunction();
    	
    	Negation neg_phi_pc = new Negation(phi_pc2);
    	innerConjunction.add((Formula) phi_pc1);
    	innerConjunction.add((Formula) neg_phi_pc);
    	
    	Conjunction clash = new Conjunction();
    	if (!existentialVars.isEmpty()) {
    		clash.add(new Exist((Formula) innerConjunction, existentialVars));
    	}
    	else {
    		clash.add(innerConjunction);
    	}
    	
    	Logger.info("***** CLASH ***** \n" + clash);
    	
    	Negation clashNegation = new Negation(clash);
    	
    	Logger.info("***** CLASH NEGATION ***** \n" + clashNegation);
    	
    	return clashNegation;
    	
    	

    	
    }
    
    public Conjunction SC_entailed(Set<OntologyConjunctiveQuery> Q) throws URISyntaxException, PredicateArityException, TermTypeException {
    	
    	
    	Conjunction SCentailed = new Conjunction();
    	Set<OntologyPredicateAtom> userQuery_atoms = SPARQL_parser(this.userQuery_sparql);
    	List<Variable> distinguishedVars = getDistinguishedVars(this.userQuery_sparql);
    	
    	OntologyConjunctiveQuery userOCQ = new OntologyConjunctiveQuery(userQuery_atoms, distinguishedVars);
    	
    	// STEP 1: First we need to check whether the user query, together with its policy 
    	// 			consequences , is entailed by the ontology
    	Disjunction phi_pc_userQuery = phi_pc(userOCQ);
    	SCentailed.add(phi_pc_userQuery);
    	
    	// Then, for each candidate clash query we build the corresponding clash formula
    	for (OntologyConjunctiveQuery candidate_clash: Q) {
    		Negation negatedClash = Clash(candidate_clash, userQuery_atoms, distinguishedVars);
    		SCentailed.add(negatedClash);
    	}
    	
    	
    	return SCentailed;
    	
    	
    }
    
    
    /*
     * SQL execution of OntologyConjunctiveQuery
     */
    
    private String format_query(String query) {
    	
    	/*
    	 * Input: sparql query
    	 * 
    	 * Output: formatted sparql query
    	 */
    	
    	/*
    	 * If the query starts with "ASK" then we replace it with "SELECT ?fakeVariable"
    	 * This is just needed for the rewriting purposes, since TreeWitness does not accept
    	 * queries starting with ASK
    	 */
    	if (query.startsWith("ASK")) {
    		Variable fake = new Variable("fakeFreeVariable");
    		query = query.replace("ASK", "SELECT ?" + fake);
    		
    	}
    	
    	/*
    	 *  Correctly format the query. Given the OntologyCOnjunctiveQuery:
    	 *  Q(x, y) :- S(x,y)
    	 *  
    	 *  the method toSparql() returns 
    	 *  SELECT ?x, ?y
    	 *  WHERE { ?x <S> ?y }
    	 *  
    	 *  Instead we need:
    	 *  SELECT ?x, ?y
    	 *  WHERE { ?x :S ?y }
    	 */
    	
    	
    	String formatted_query = "";
    	formatted_query = query.replace(">", "");
        formatted_query = formatted_query.replace("<", ":");
    	
        return formatted_query;
    }
    
    public void sql_exec_OCQ(Conjunction SCentailed) throws PredicateArityException, TermTypeException, URISyntaxException, SQLificationException, DriverNotFoundException, SQLException {
    	
    	/*
    	 * Takes in input an OntologyConjunctiveQuery, rewrites it, generates the corresponding sql query and executes it
    	 */
    	Set<Table> tables = new HashSet<>();
    	
    	// Initialize DB schema
    	for (OWLAxiom a: tbox.getAxioms()) {
    		if (a instanceof OWLDeclarationAxiom) {
    			OWLDeclarationAxiom oda = (OWLDeclarationAxiom) a;
    			OWLEntity entity = oda.getEntity();
    			
    			if (entity.isOWLClass()) {
    				List<String> attributesNames = new ArrayList<>();
    				attributesNames.add("obj");
    				tables.add(new Table(entity.getIRI().getShortForm(), attributesNames));
    			}
    			// I think I will have only OWLObjectProperties
    			else if (entity.isOWLObjectProperty() || entity.isOWLDataProperty()) {
    				List<String> attributesNames = new ArrayList<>();
    				attributesNames.add("obj1");
    				attributesNames.add("obj2");
    				tables.add(new Table(entity.getIRI().getShortForm(), attributesNames));
    			}
    		}
    	}
    	
    	DBSchema schema = new DBSchema("dbName", tables);
    
    	
    	Formula f = (Formula) SCentailed;
    	f.unbindVariables();
    	
    	boolean distinct = true; 
    	String q = new SQLCompiler(schema).sqlify(f, new HashMap<>(), distinct);
    	String q1 = cleanConstantsName(q);
    	Logger.info("SQL Query: \n" + q1);
    	
    	sqlExecution(q1);
    	
    
    	
    }
    
    public int sqlExecution(String sqlQuery) throws DriverNotFoundException, SQLException {
    	
    	/*
    	 * Takes an SQL query and executes it over the relational database
    	 */
    	
    	/*
    	 * Uncomment to test connection first
    	 * 
    	Logger.debug("Testing connection ...");
    	SQLConnection.testConnection(configuration);
    	Logger.debug("Testing went fine ...");
    	*/
    
    	
    	Connection connection = new SQLConnection(configuration).getConnection();   
    	Statement stmt = connection.createStatement();
    	stmt.setQueryTimeout(3600); // 1 hour
    	ResultSet rs = null;
    	long startExecutionTime = System.nanoTime();
    	try {
    		rs = stmt.executeQuery(sqlQuery);
    	} catch (SQLException e) {
    		// handle timeout exceptions
    		if (e.getMessage().toLowerCase().contains("timeout")) {
    			Logger.info("SQL EXECUTION TIME: TIMEOUT REACHED");
    			return -1;
    		}
    		e.printStackTrace();
    	}
    	
    	Logger.info("Query executed");
    	
    	long endExecutionTime = System.nanoTime();
    	Logger.info("SQL EXECUTION TIME: " +
                (endExecutionTime - startExecutionTime) / 1_000_000 + " milliseconds");
    	
    	
    	
    	boolean print = true;		// → to print the result
    	int counter = printResultSet(rs, print);
    	
    	Logger.info("Number of answers: " + counter);
    	
    	return counter;
    	
    }
    
    
    private int printResultSet(ResultSet rs, boolean print) throws SQLException {
        ResultSetMetaData meta = rs.getMetaData();
        int cols = meta.getColumnCount();

        if (print) {
		    // header
		    for (int i = 1; i <= cols; i++) {
		        System.out.print(meta.getColumnLabel(i) + " |" + "\t");
		    }
		    System.out.println();
        }

        int counter = 0;
        // rows
        while (rs.next()) {
        	if (print) {
		        for (int i = 1; i <= cols; i++) {
		            System.out.print(rs.getString(i) + " |" + "\t");
		        }
		        System.out.println();
        	}
        	counter++;
        }
        
        return counter;
    }
    
    

    
    private String cleanConstantsName(String s) {
        String regex = "\"[^\\s#]+#([^\\s#]+)\"";
        Pattern pattern = Pattern.compile(regex);
        Matcher matcher = pattern.matcher(s);
        while (matcher.find()) {
            String constantName = matcher.group(1);
            s = s.replace(matcher.group(), '"' + constantName + '"');
        }
        return s;
    }
    
    
    
    
    
    
}
