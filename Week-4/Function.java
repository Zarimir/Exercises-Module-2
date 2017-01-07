/**
 * 
 */
package ss.week4.math;

/**
 * @author Zarry
 * @version 3.0
 */
public interface Function {
	
	/**
	 * Executes the function to an argument of type double.
	 * @param argument of type double
	 * @return result of type double
	 */
	public double apply(double argument);
	
	/**
	 * Returns the Function of the derivative of the Function.
	 * @return Function
	 */
	public Function derivative();
}
