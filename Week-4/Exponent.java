/**
 * 
 */
package ss.week4.math;

/**
 * @author Zarry
 * @version 3.0
 */
public class Exponent implements Function, Integrandable {
	
	// ------------------------ Instance Variables ------------------------
	
	/**
	 * Instance Variables.
	 * @param exp the exponent of the function
	 */
	private int exp;
	
	// ------------------------ Constructor ------------------------
	
	/**
	 * Constructor.
	 * @param exponent the exponent of the function
	 */
	public Exponent(int exponent) {
		this.exp = exponent;
	}
	
	/**
	 * toString().
	 */
	//@ ensures \result != null;
	public String toString() {
		return "x" + "^" + this.exp;
	}
	
	// ------------------------ Function Implementation ------------------------
	
	/**
	 * Raises the argument to the power of exp.
	 * @param argument of type double
	 * @return argument^exp;
	 */
	public double apply(double argument) {
		double result = 1;
		for (int i = 1; i <= exp; i++) {
			result = result * argument;
		}
		return result;
	}
	
	/**
	 * The derivative of this function.
	 * @return new LinearProduct of new Exponent and new Constant()
	 */
	//@ ensures \result != null;
	public Function derivative() {
		return new LinearProduct(new Constant(this.exp), new Exponent(this.exp - 1));
	}
	
	// ------------------------ Integrandable Implementation ------------------------
	
	/**
	 * Returns a Function which is the Integrand of this function.
	 * @return new LinearProduct
	 */
	//@ ensures \result != null;
	public Function integrand() {
		return new LinearProduct(new Constant((double) 1 / (this.exp + 1)),
				new Exponent(this.exp + 1));
	}
}
