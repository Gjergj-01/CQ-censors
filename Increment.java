package cqcensors;

import java.util.Arrays;

public class Increment {
	
	/*
	 * This is just an auxiliary class implementing two auxiliary functions:
	 * 		- Increment all
	 * 		- Increment-all-non zeros
	 * 
	 * 		Such functions will be useful to explore all the possible combinations of homomorphisms
	 */
	
	public static int[] Increment_all(int[] a, int[] k) {
        if (Arrays.equals(a,k)) { 
            return a;
        }

        int l = a.length;
        int[] aux = a.clone();

        int i = l - 1; 

        while (i >= 0) {
            if (aux[i] < k[i]) {
                aux[i] += 1; 
                return aux;
            }
            else {
                i -= 1; 
                if (i >= 0) {
                    for (int j = i+1; j < l; j++) {
                        aux[j] = 0;
                    }
                }
            }
        }

        return a;
	}
	
	
	
	public static int[] Increment_all_non_zeros(int[] a, int[] k) {
        if (Arrays.equals(a,k)) { 
            return a;
        }

        int l = a.length;
        int[] aux = a.clone();

        int i = l - 1; 

        while (i >= 0) {
            if (aux[i] < k[i]) {
                aux[i] += 1; 
                return aux;
            }
            else {
                i -= 1; 
                if (i >= 0) {
                    for (int j = i+1; j < l; j++) {
                        aux[j] = 1;
                    }
                }
            }
        }

        return a;
    }
          
	
	public static void printArray(int[] array) {
        int len = array.length;
        System.out.print("[");
        for (int i = 0; i < len; i++) {
            System.out.print(array[i] + " ");
        }
        System.out.print("]");
	}

}
