/**
 * 
 */
package ss.week4.math;

/**
 * @author Zarry
 * @version 3.0
 */
public class Constant implements Function, Integrandable {
	
	// ------------------------ Instance Variables ------------------------
	
	/**
	 * Instance Variables.
	 * @param constant the constant of this function
	 */
	private double constant;
	
	// ------------------------ Constructor ------------------------
	
	/**
	 * Constructor.
	 * Pass the constant as an argument
	 * @param c argument of type double
	 */
	public Constant(double c) {
		this.constant = c;
	}
	
	/**
	 * toString().
	 */
	//@ ensures \result != null;
	public String toString() {
		return "" + this.constant;
	}
	
	// ------------------------ Function Implementation ------------------------
	
	/**
	 * Apply the constant function returns the constant.
	 */
	public double apply(double argument) {
		return this.constant;
	}
	
	/**
	 * The derivative of a constant is a constant 0.
	 */
	//@ ensures \result != null;
	public Function derivative() {
		return new Constant(0);
	}
	
	// ------------------------ Integrandable Implementation ------------------------
	
	/**
	 * Returns Function which is the integrand of the original function
	 * @return Function
	 */
	//@ ensures \result != null;
	public Function integrand() {
		return new LinearProduct(new Constant(this.constant), new Exponent(1));
	}
}
