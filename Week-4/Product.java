/**
 * 
 */
package ss.week4.math;

/**
 * @author Zarry
 * @version 3.0
 */
public class Product implements Function {
	
	// ------------------------ Instance Variables ------------------------
	
	/**
	 * Instance Variables.
	 * @param f function 1
	 * @param g function 2
	 */
	//@ private invariant f != null;
	//@ private invariant g != null;
	private Function f;
	private Function g;
	
	// ------------------------ Constructor ------------------------
	
	/**
	 * Constructor.
	 * Takes 2 Functions as parameters
	 * @param funct1 function 1
	 * @param funct2 function 2
	 */
	//@ requires funct1 != null;
	//@ requires funct2 != null;
	public Product(Function funct1, Function funct2) {
		this.f = funct1;
		this.g = funct2;
	}
	
	/**
	 * toString().
	 */
	//@ ensures \result != null;
	public String toString() {
		return "" + this.f + " * " + this.g;
	}
	
	// ------------------------ Queries ------------------------
	
	/**
	 * getF()
	 * @return f
	 */
	//@ ensures \result != null;
	public Function getF() {
		return this.f;
	}
	
	/**
	 * getG()
	 * @return g
	 */
	//@ ensures \result != null;
	public Function getG() {
		return this.g;
	}
	
	// ------------------------ Function Implementation ------------------------
	
	/**
	 * Apply the argument of type double to f and g and returns the product.
	 * @param argument
	 * @return
	 */
	public double apply(double argument) {
		return f.apply(argument) * g.apply(argument);
	}
	
	/**
	 * Returns a Sum of the products f' * g and f * g'
	 * @return new Sum(Product, Product)
	 */
	//@ ensures \result != null;
	public Function derivative() {
		return new Sum(new Product(f.derivative(), g), new Product(f, g.derivative()));
	}
}
