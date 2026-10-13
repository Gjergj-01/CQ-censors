package cqcensors;

import java.util.ArrayList;

public class Increment {
	
	/*
	 * This is just an auxiliary class implementing two auxiliary functions:
	 * 		- Increment all
	 * 		- Increment-all-non zeros
	 * 
	 * 		Such functions will be useful to explore all the possible combinations of homomorphisms
	 */
	
	public static ArrayList<Integer> Increment_all(ArrayList<Integer> a, ArrayList<Integer> k) {
        if (a.equals(k)) { 
            return a;
        }

        int l = a.size();
        @SuppressWarnings("unchecked")
		ArrayList<Integer> aux = (ArrayList<Integer>) a.clone();

        int i = l - 1; 

        while (i >= 0) {
            if (aux.get(i) < k.get(i)) {
                aux.set(i, aux.get(i)+1); 
                return aux;
            }
            else {
                i -= 1; 
                if (i >= 0) {
                    for (int j = i+1; j < l; j++) {
                        aux.set(j, 0);
                    }
                }
            }
        }

        return a;
	}
	
	
	
	public static ArrayList<Integer> Increment_all_non_zeros(ArrayList<Integer> a, ArrayList<Integer> k) {
        if (a.equals(k)) { 
            return a;
        }

        int l = a.size();
        @SuppressWarnings("unchecked")
		ArrayList<Integer> aux = (ArrayList<Integer>) a.clone();

        int i = l - 1; 

        while (i >= 0) {
            if (aux.get(i) < k.get(i)) {
                aux.set(i, aux.get(i)+1); 
                return aux;
            }
            else {
                i -= 1; 
                if (i >= 0) {
                    for (int j = i+1; j < l; j++) {
                        aux.set(j, 1);
                    }
                }
            }
        }

        return a;
    }
         

}
