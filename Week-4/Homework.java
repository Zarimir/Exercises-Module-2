/**
 * 
 */
package ss.week4.math;

/**
 * @author Zarry
 * @version 3.0
 */
public class Homework {
	
	// ------------------------ Main ------------------------
	
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		LinearProduct f1 = new LinearProduct(new Constant(4), new Exponent(4));
		Function f2 = f1.integrand();
		Function f3 = f1.derivative();
		System.out.println("f(x) = " + f1 + ", f(8) =  " + f1.apply(8));
		System.out.println("f(x) = " + f2 + ", f(8) =  " + f2.apply(8));
		System.out.println("f(x) = " + f3 + ", f(8) =  " + f3.apply(8));

	}

}
