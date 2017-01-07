package ss.week4.test;

import org.junit.Test;
import ss.week4.math.*;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;


public class PolynomialTest {
	public static final int CONSTANT = 2;
    private static final double DELTA = 1e-15;
    private static final double[] ARGS = {2, 2, 2, 2, 2, 2, 2, 2};
    private Polynomial obj1 = new Polynomial((int) CONSTANT / CONSTANT, ARGS);
    private Polynomial obj2 = new Polynomial(CONSTANT, ARGS);
    private Polynomial obj3 = new Polynomial(CONSTANT * CONSTANT, ARGS);
    
    @Test
    public void testApply() {
        assertEquals(6, obj1.apply(CONSTANT), DELTA);
        assertEquals(14, obj2.apply(CONSTANT), DELTA);
        assertEquals(62, obj3.apply(CONSTANT), DELTA);
    }

    @Test
    public void testDerivative() {
        assertTrue(obj1.derivative() instanceof Sum);
    	assertEquals(2, obj1.derivative().apply(2), DELTA);
        assertEquals(10, obj2.derivative().apply(2), DELTA);
        assertEquals(98, obj3.derivative().apply(2), DELTA);
    }
    
    @Test
    public void testIntegrand() {
    	assertEquals(8, obj1.integrand().apply(CONSTANT), DELTA);
    	double[] a = {2, 0, 2, 2, 2, 2};
    	Polynomial obj = new Polynomial(3, a);
    	assertEquals(16, obj.integrand().apply(CONSTANT), DELTA);
    }
    
}
