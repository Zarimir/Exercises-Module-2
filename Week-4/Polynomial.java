/**
 * 
 */
package ss.week4.math;

/**
 * @author Zarry
 * @version 3.0
 */
public class Polynomial implements Function {
	
	public static void main(String[] args) {
		double[] a = {2, 2, 2, 2, 2, 2, 2, 2, 2};
		Polynomial obj = new Polynomial(1, a);
		System.out.println(obj);
		System.out.println(obj.integrand());
		
	}
	
	// ------------------------ Instance Variables ------------------------
	
	/**
	 * Instance Variables.
	 * @param f new Sum()
	 */
	//@ private invariant f != null;
	private Sum f;
	
	// ------------------------ Constructor ------------------------
	
	/**
	 * Constructor.
	 * Polynomial is Sum of Sums of Constants and Exponents
	 * @param exp the exponent of the polynomial
	 * @param args the arguments of the polynomial
	 */
	//@ requires exp >= 0 && exp < args.length; 
	public Polynomial(int exp, double[] args) {
		LinearProduct holder = new LinearProduct (new Constant(args[0]), new Exponent(exp));
		Sum obj = new Sum(new Constant(0), holder);
		for (int i = 1; i <= exp; i++) {
			holder = new LinearProduct (new Constant(args[i]), new Exponent(exp - i));
			obj = new Sum(obj, holder);
		}
		this.f = obj;
	}
	
	/**
	 * toString().
	 */
	//@ ensures \result != null;
	public String toString() {
		return "" + this.f;
	}
	
	// ------------------------ Function Implementation ------------------------
	
	/**
	 * Apply argument of type double to the Polynomial function.
	 */
	public double apply(double argument) {
		return this.f.apply(argument);
	}
	
	/**
	 * Returns the derivative of the Polynomial function.
	 * @return derivative of the sum of this function
	 */
	//@ ensures \result != null;
	public Function derivative() {
		return this.f.derivative();
	}
	
	// ------------------------ Integrandable Implementation ------------------------
	
	/**
	 * Returns the integrand of the sum of this function.
	 * @return new Function
	 */
	public Function integrand() {
		return this.f.integrand();
	}
}
