/**
 * 
 */
package ss.week4.math;

/**
 * @author Zarry
 *
 */
public class LinearProduct extends Product implements Integrandable{
	
	// ------------------------ Constructor ------------------------
	
	/**
	 * Constructor.
	 * @param funct1 function 1
	 * @param funct2 function 2
	 */
	//@ requires funct1 != null
	//@ requires funct2 != null;
	public LinearProduct(Constant funct1, Function funct2) {
		super(funct1, funct2);
	}
	
	// ------------------------ Function Implementation ------------------------
	
	/**
	 * The derivative of a LinearProduct.
	 */
	//@ ensures \result != null;
	public Function derivative() {
		return new LinearProduct((Constant) this.getF(), this.getG().derivative());
	}
	
	// ------------------------ Integrandable Implementation ------------------------
	
	/**
	 * Returns the integrand of this function or null if there is none.
	 * @return Function
	 */
	public Function integrand() {
		if (this.getG() instanceof Integrandable) {
			return new LinearProduct((Constant) this.getF(),
					((Integrandable) this.getG()).integrand());
		}
		return null;
	}
}
