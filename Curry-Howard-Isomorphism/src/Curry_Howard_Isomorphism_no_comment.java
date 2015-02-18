
public class Curry_Howard_Isomorphism {
    
	public class P{}
	
	public class Q{}
	
	public class R{}
	
	public class And<T1, T2>{
		private T1 v1;
		private T2 v2;
		
		public And(T1 x, T2 y){
			v1 = x;
			v2 = y;
		}

		public T1 and_e1(){
			return v1;
		}
		
		public T2 and_e2(){
			return v2;
		}		
	}

	public class Or<T1, T2>{
		public Or(){}
		
		public T1 left() { return null; }
		public T2 right() { return null; }
		
		public class Left<T1, T2> extends Or<T1, T2>{
			private T1 v;
			public Left(T1 v1) { v = v1; }
			public T1 left() { return v; }
		}
		
		public class Right<T1, T2> extends Or<T1, T2>{
			private T2 v;
			public Right(T2 v2) { v = v2; }
			public T2 right() { return v; }
		}
		
		public Or<T1, T2> or_i1(T1 v1){
			return (new Left<T1, T2>(v1));
		}

		public Or<T1, T2> or_i2(T2 v2){
			return (new Right<T1, T2>(v2));
		}

		public <T3> T3 or_e(Deduction<T1, T3> d1, Deduction<T2, T3> d2){
			if(this instanceof Left){
				return d1.apply(this.left());
			}else{
				return d2.apply(this.right());
			}
		}
	}
	
	public abstract class Deduction<T1, T2>{
		public abstract T2 deduction_step(T1 assumptions);
		
		public T2 apply(T1 v1){
			return deduction_step(v1);
		}
	}
	
	public class Imply<T1, T2>{
		private Deduction<T1, T2> deduction;

		public Imply(Deduction<T1, T2> d){
			deduction = d;
		}
		
		public T2 imply_e(T1 v){
			return deduction.apply(v);
		}
		
	}
	
	/*****************************************************************/
	/********************** Proofs-As-Programs  **********************/
	/*****************************************************************/	
	
	
	/*****************************************************************/
	/**                     Examples of Deduction                    */
	/*****************************************************************/	

	/**
	 * ----------- Proofs -------------
	 * p ^ q  |-  q ^ p
	 * 
	 * 1. p ^ q                 premise
	 * 2. p                      ^e1 1
	 * 3. q                      ^e2 1
	 * 4. q ^ p                  ^i 3,2
	 **/
	public And<Q, P> and_example(And<P, Q> pANDq){
		// premise: pANDq        
		P p = pANDq.and_e1();                // ^e1
		Q q = pANDq.and_e2();                // ^e2
		And<Q, P> qANDp = new And<Q, P>(q, p);	 // ^i
		return qANDp;
	}
	
	/**
	 * ----------- Proofs -------------
	 * q  |-  p v q v r
	 * 
	 * 1. q                    premise
	 * 2. p v q                  vi2 1
	 * 3. p v q v r              vi1 2
	 **/
	public Or<Or<P, Q>, R> or_example(Q q){
		Or<P, Q> pq = new Or<P, Q>();
		Or<P, Q> pORq = pq.or_i2(q);                   // vi2
		Or<Or<P, Q>, R> pqr = new Or<Or<P, Q>, R>();
		Or<Or<P, Q>, R> pORqORr = pqr.or_i1(pORq);     // vi1
		return pORqORr;
	}
	
	
	/**
	 * ----------- Proofs -------------
	 * (p ^ q) -> r,  p --> q,  p  |-  r
	 * 
	 * 1. (p ^ q) -> r           premise
	 * 2. p                      premise
	 * 3. p -> q                 premise
	 * 4. q                      ->e 3,2
	 * 5. p ^ q                  ^i 2,4
	 * 6. r                      ->e 1,5 
	 **/
	public R example1(Imply<And<P, Q>, R> pqIMPLYr, Imply<P, Q> pIMPLYq, P p){
		Q q = pIMPLYq.imply_e(p);        // ->e
		And<P, Q> pANDq = new And<P, Q>(p, q);         // ^i
		R r = pqIMPLYr.imply_e(pANDq);   // ->e
		return r;
	}
	
	/**
	 * ----------- Proofs -------------
	 * (p v q) -> r,  q |-  r
	 * 
	 * 1. (p v q) -> r        premise
	 * 2. q                   premise
	 * 3. p v q               vi2 2
	 * 4. r                   ->e 1,3
	 **/
	public R example11(Imply<Or<P, Q>, R> pqIMPLYr, Q q){
		Or<P, Q> pq = new Or<P, Q>();
		Or<P, Q> pORq = pq.or_i2(q);      // vi2
		R r = pqIMPLYr.imply_e(pORq);     // ->e
		return r;
	}
	
	/**
	 * ----------- Proofs -------------
	 * p,  (q ^ p) -> r  |-  q -> r 
	 * 
	 * 1. p                      premise
	 * 2. (q ^ p) -> r           premise
	 * ... 3. q                  assumption
	 * ... 4. q ^ p              ^i 3,1
	 * ... 5. r                  ->e 2,4
	 * 6. q -> r                 ->i 3-5
	 **/
	public Imply<Q, R> example12(P p, Imply<And<Q, P>, R> qpIMPLYr){
		Deduction<Q, R> qDEDUCEr = 
				new Deduction<Q, R>(){
					public R deduction_step(Q q){
						And<Q, P> qANDp = new And<Q, P>(q, p);  // ^i
						R r = qpIMPLYr.imply_e(qANDp);
						return r;
					}
				};
		Imply<Q, R> qIMPLYr = new Imply<Q, R>(qDEDUCEr);        // ->i
		return qIMPLYr;
	}

	/**
	 * ----------- Proofs -------------
	 * p --> r,  q --> r  |-  (p v q) --> r

	 * 1. p --> r            premise
	 * 2. q --> r            premise
	 * ... 3. p v q               assumption

	 * ... ... 4. p                       assumption
	 * ... ... 5. r                       -->e 1,4

	 * ... ... 6. q                       assumption
	 * ... ... 7. r                       -->e 2,6

	 * ... 8. r                    ve 3,4-5,6-7
	 * 9. (p v q) --> r     -->i 3-8
	 **/
	public Imply<Or<P, Q>, R> example2(Imply<P, R> pIMPLYr, Imply<Q, R> qIMPLYr){
		Deduction<Or<P, Q>, R> pqDEDUCEr = 
				new Deduction<Or<P, Q>, R>(){
					public R deduction_step(Or<P, Q> pORq){
						// assume P ---> R
						Deduction<P, R> pDEDUCEr = 
								new Deduction<P, R>(){
									public R deduction_step(P p){
										R r = pIMPLYr.imply_e(p);   // ->e
										return r;
									}
								};
								
						// assume Q ---> R		
						Deduction<Q, R> qDEDUCEr = 
								new Deduction<Q, R>(){
									public R deduction_step(Q q){
										R r = qIMPLYr.imply_e(q);   // ->e
										return r;
									}
								};
								
						R r = pORq.or_e(pDEDUCEr, qDEDUCEr);
						return r;
					}
				};
		
		Imply<Or<P, Q>, R> pqIMPLYr = new Imply<Or<P, Q>, R>(pqDEDUCEr);  // ->i
		return pqIMPLYr;
	}
	
	/**
	 * ----------- Proofs -------------
	 * q |- p -> (q ^ p)

	 * 1. q               premise
	 * ... 2. p           assumption      ...apply the ->i tactic
	 * ... 3. q ^ p       ^i 1,2
	 * 4. p -> (q ^ p)    ->i 2-3
	 **/
	public Imply<P, And<Q, P>> example3(Q q){
		Deduction<P, And<Q, P>> pDEDUCEqp = 
				new Deduction<P, And<Q, P>>(){
					public And<Q, P> deduction_step(P p){
						And<Q, P> qANDp = new And<Q, P>(q, p);  // ^i
						return qANDp;
					}
				};
		
		Imply<P, And<Q, P>> pIMPLYqp = new Imply<P, And<Q, P>>(pDEDUCEqp); // ->i
		return pIMPLYqp;
	}
	
	/**
	 * ----------- Proofs -------------
	 * p -> (q -> r) |- (p -> q) -> (p -> r)

	 * 1. p -> (q -> r)     premise
	 * ... 2. (p -> q)      assumption    ...apply the ->i tactic
	 * 		... 3. p         assumption
     *		... 4. q -> r    ->e 1,3
     *		... 5. q         ->e 2,3
     *		... 6. r         ->e 4,5
	 * ... 7. p -> r        ->i 3-6
	 * 8. (p -> q) -> (p -> r)
	 **/
	public Imply<Imply<P, Q>, Imply<P, R>> example4(Imply<P, Imply<Q, R>> pIMPLYqir){
		Deduction<Imply<P, Q>, Imply<P, R>> piqDEDUCEpir = 
				new Deduction<Imply<P, Q>, Imply<P, R>>(){
					public Imply<P, R> deduction_step(Imply<P, Q> pIMPLYq){
						// assume P --> R
						Deduction<P, R> qDEDUCEr = 
								new Deduction<P, R>(){
									public R deduction_step(P p){
										Imply<Q, R> qIMPLYr = pIMPLYqir.imply_e(p);  // ->e
										Q q = pIMPLYq.imply_e(p);                    // ->e
										R r = qIMPLYr.imply_e(q);                    // ->e
										return r;
									}
								};
						// Imply introduction
						Imply<P, R> pIMPLYr = new Imply<P, R>(qDEDUCEr);             // ->i
						return pIMPLYr;
					}
				};
		
		Imply<Imply<P, Q>, Imply<P, R>> piqIMPLYpir = new Imply<Imply<P, Q>, Imply<P, R>>(piqDEDUCEpir);  // ->i
		return piqIMPLYpir;
	}
}




