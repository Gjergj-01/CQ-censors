package cqcensors;

import cqcensors.fol.*;
import cqcensors.fol.DataConstant.DatatypeNoMatchException;
import java.util.regex.Pattern;
import java.util.regex.Matcher; 
import java.util.*;

public class SPARQLParser {
	
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
	    
	    Returns: {R(x,y), Professor(y), Person(y)}
 
	 */
	
	private static final String membership_assertion = "rdf:type";
    private static final String membership_assertion_shorten = "a";
    
    // Regex matching a Basic Graph Pattern (BGP) in a sparql query

    private static final String BGP_regex = "(\\?\\w+|\\w+)\\s+(:?\\w+|rdf:type|a)\\s+(\\?\\w+|:?\\w+)\\s*\\.";  
    
	
	public static Set<PredicateAtom> SPARQL_parser(String sparql) {
		
		Set<PredicateAtom> atoms = new HashSet<>();
		
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
                    	System.out.println("Type mismatch: SPARQL query is malformed!");
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
                    	System.out.println("Type mismatch: SPARQL query is malformed!");
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
            			System.out.println("Type mismatch: SPARQL query is malformed!");
            		}
            		
            	}

            }

        }

        if (!found) Logger.info("The SPARQL query did not match with a BGP, probably it is maformed! \nPrinting the query:\n " + sparql);
        
        return atoms;
		
	}

}
