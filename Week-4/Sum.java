/**
 * 
 */
package ss.week4.math;

/**
 * @author Zarry
 * @version 3.0
 */
public class Sum implements Function, Integrandable {
	
	// ------------------------ Instance Variables ------------------------
	
	/**
	 * Instance Variables.
	 * @param f the first function of the sum
	 * @param g the second function of the sum
	 */
	//@ private invariant f != null;
	//@ private invariant g != null;
	private Function f;
	private Function g;
	
	// ------------------------ Constructor ------------------------
	
	/**
	 * Constructor.
	 * Constructs the sum of 2 functions
	 * @param funct1 the first function
	 * @param funct2 the second function
	 */
	//@ requires funct1 != null;
	//@ requires funct2 != null;
	public Sum(Function funct1, Function funct2) {
		this.f = funct1;
		this.g = funct2;
	}
	
	/**
	 * toString().
	 */
	//@ ensures \result != null;
	public String toString() {
		return "" + f + " + " + g;
	}
	
	// ------------------------ Function Implementation ------------------------
	
	/**
	 * Apply the argument to the 2 functions of function Sum and return the sum.
	 * @param argument of type double
	 * @return the sum of the .apply of the 2 functions
	 */
	public double apply(double argument) {
		return f.apply(argument) + g.apply(argument);
	}
	
	/**
	 * Returns new Sum of the derivative of the functions
	 * of the original Sum.
	 * @return new Sum
	 */
	//@ ensures \result != null;
	public Function derivative() {
		return new Sum(f.derivative(), g.derivative());
	}
	
	// ------------------------ Integrandable Implementation ------------------------
	
	/**
	 * Returns new Sum of the integrands of the functions f and g.
	 * @return new Sum
	 */
	public Function integrand() {
		if (this.f instanceof Integrandable && this.g instanceof Integrandable) {
			return new Sum(((Integrandable) this.f).integrand(),
					((Integrandable) this.g).integrand());		
		}
		return null;
	}
}
