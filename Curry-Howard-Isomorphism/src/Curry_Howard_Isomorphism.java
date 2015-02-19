import Curry_Howard_Isomorphism.Or.Left;
import Curry_Howard_Isomorphism.Or.Right;


public class Curry_Howard_Isomorphism {
	public class P{}
	
	public class Q{}
	
	public class R{}
	
	/**
	 * To illustrate the relationship between proofs and programs, as described by Curry–Howard isomorphism, 
	 * we introduce the following judgment:
	 *  V: T         V is a proof term for proposition T, which can also be interpreted as
	 *  V: T         V is a program of type T
	 *  
	 *  These dual interpretations of the same judgment is the core of the Curry-Howard isomorphism 
	 *  (or the proofs-as-programs and propositions-as-types interpretation). 
	 **/
	
	/*****************************************************************/
	/********************* Propositions-As-Types  ********************/
	/*****************************************************************/		
	

	/* ### Deduction Rules (Inference Rules) ### */
	
	
	/*****************************************************************/
	/**         And-introduction and And-elimination Rules           */
	/*****************************************************************/	
	
	public class And<T1, T2>{
		private T1 v1;
		private T2 v2;
		
		/**
		 * 'And' is a program of type T1 -> T2 -> AND<T1, T2>, taking a value of type T1 and T2 respectively
		 * and producing a value of type AND<T1, T2>;
		 * 
		 * by Curry-Howard isomorphism, if T1 and T2 are propositions, then it can be interpreted as taking a proof 
		 * of proposition T1 and T2 respectively and producing a proof of proposition AND<T1, T2>.
		 * This corresponds to And-introduction rule:
		 * 
		 *  T1  T2
		 * -------- (^i)
		 *  T1 ^ T2
		 **/		
		public And(T1 x, T2 y){
			v1 = x;
			v2 = y;
		}
		
		/**
		 * 'end_e1' is a program of type AND<T1, T2> -> T1, taking a value of type AND<T1, T2> and producing a value of type T1;
		 * 
		 * by Curry-Howard isomorphism, if T1 and T2 are propositions, then it can be interpreted as taking a proof 
		 * of proposition AND<T1, T2> and producing a proof of proposition T1.
		 * This corresponds to And-elimination rule:
		 * 
		 *  T1 ^ T2
		 *  ------- (^e1)
		 *    T1
		 **/
		public T1 and_e1(){
			return v1;
		}
		
		
		/**
		 * 'and_e2' is a program of type AND<T1, T2> -> T2, taking a value of type AND<T1, T2> and producing a value of type T2;
		 * 
		 * by Curry-Howard isomorphism, if T1 and T2 are propositions, then it can be interpreted as taking a proof 
		 * of proposition AND<T1, T2> and producing a proof of proposition T2.
		 * This corresponds to And-elimination rule:
		 * 
		 *  T1 ^ T2
		 *  ------- (^e2)
		 *    T2
		 **/
		public T2 and_e2(){
			return v2;
		}		
	}

	/*****************************************************************/
	/**           Or-introduction and Or-elimination Rules           */
	/*****************************************************************/	
	
	/**
	 * for any types T1 and T2,
	 * Or T1 T2, written T1 + T2, is the disjoint type sum of T1 and T2, which is defined in OCaml as:
	 *   Inductive Or (T1 T2:Type) : Type :=
	 *     | or_i1 : T1 -> Or T1 T2  
	 *     | or_i2 : T2 -> Or T1 T2.
	 *   where or_i1 and or_i2 are type constructors, which are used to make both T1 and T2 as subtype of (Or T1 T2)
	 *   and (Or T1 T2) = T1 + T2
	 * 
	 * Or<T1, T2> = Left<T1, T2> + Right<T1, T2>
	 * 
	 **/
	public static class Or<T1, T2>{
		public Or(){}
		
		public T1 left() { return null; }
		public T2 right() { return null; }
		
		public static class Left<T1, T2> extends Or<T1, T2>{
			private T1 v;
			public Left(T1 v1) { v = v1; }
			public T1 left() { return v; }
		}
		
		public static class Right<T1, T2> extends Or<T1, T2>{
			private T2 v;
			public Right(T2 v2) { v = v2; }
			public T2 right() { return v; }
		}
		
		/**
		 * 'or_i1' is a program of type T1 -> Or<T1, T2>, taking a value of type T1 and 
		 * producing a value of type Or<T1, T2>;
		 * 
		 * by Curry-Howard isomorphism, if T1 and T2 are propositions, then it can be interpreted as taking a proof 
		 * of proposition T1 and producing a proof of proposition Or<T1, T2>.
		 * This corresponds to Or-elimination rule:
		 * 
		 *    T1
		 *  ------- (vi1)
		 *  T1 v T2
		 **/
		public static <T1, T2> Or<T1, T2> or_i1(T1 v1){
			return (new Left<T1, T2>(v1));
		}
		
		/**
		 * 'or_i2' is a program of type T2 -> Or<T1, T2>, taking a value of type T2 and 
		 * producing a value of type Or<T1, T2>;
		 * 
		 * by Curry-Howard isomorphism, if T1 and T2 are propositions, then it can be interpreted as taking a proof 
		 * of proposition T2 and producing a proof of proposition Or<T1, T2>.
		 * This corresponds to Or-elimination rule:
		 * 
		 *    T2
		 *  ------- (vi2)
		 *  T1 v T2
		 **/
		public static <T1, T2> Or<T1, T2> or_i2(T2 v2){
			return (new Right<T1, T2>(v2));
		}
		
		/**
		 *            ...T1 assume   ...T2 assume
		 *  T1 v T2   ...T3          ...T3
		 * --------------------------------------- (ve)
		 *                    T3
		 **/
		public <T3> T3 or_e(Deduction<T1, T3> d1, Deduction<T2, T3> d2){
			if(this instanceof Left){
				return d1.apply(this.left());
			}else{
				return d2.apply(this.right());
			}
		}
	}

	/*****************************************************************/
	/**        Implies-introduction and Implies-elimination          */
	/*****************************************************************/		
	
	public abstract class Deduction<T1, T2>{
		public abstract T2 deduction_step(T1 assumptions);
		
		public T2 apply(T1 v1){
			return deduction_step(v1);
		}
	}
	
	public class Imply<T1, T2>{
		private Deduction<T1, T2> deduction;
		
		/**
		 * 'imply_i' is a program of type T1 -> T2, taking a value of type T1 and producing a value of T2; 
		 * 
		 * by Curry-Howard isomorphism, if T1 and T2 are propositions, then it means taking a proof of 
		 * proposition T1 and producing a proof of proposition T2.
		 * This corresponds to Implies-introduction:
		 * 
		 *  ... T1 assume
		 *  ... T2
		 * -------------- (->i)
		 *   T1 -> T2
		 **/
		public Imply(Deduction<T1, T2> d){
			deduction = d;
		}
		
		
		/**
		 * 'imply_e' is a program of type Imply<T1, T2> -> T1 -> T2, taking a value of type Imply<T1, T2> and T1 
		 * respectively and producing a value of T2; 
		 * 
		 * by Curry-Howard isomorphism, if T1 and T2 are propositions, then it means taking a proof of 
		 * proposition T1 and producing a proof of proposition T2.
		 * This corresponds to Implies-elimination:
		 *  
		 *  T1 -> T2
		 *  T1
		 *  -------- (->e)
		 *     T2
		 **/
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
		// premise: And<P, Q> pANDq             // line 1
		P p = pANDq.and_e1();                   // line 2 ^e1 applied to P ^ Q
		Q q = pANDq.and_e2();                   // line 3 ^e2 applied to P ^ Q
		And<Q, P> qANDp = new And<Q, P>(q, p);	// line 4 ^i  applied to Q and P
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
		// premise: Q q                                // line 1
		Or<P, Q> pORq = Or.or_i2(q);                   // line 2 vi2 applied to Q
		Or<Or<P, Q>, R> pORqORr = Or.or_i1(pORq);     // line 3 vi1 applied to P v Q
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
		// premise: Imply<And<P, Q>, R> pqIMPLYr   // line 1
		// premise: Imply<P, Q> pIMPLYq            // line 3
		// premise: P p                            // line 2
		Q q = pIMPLYq.imply_e(p);                  // line 4 ->e applied to P -> Q and P
		And<P, Q> pANDq = new And<P, Q>(p, q);     // line 5 ^i  applied to P and Q
		R r = pqIMPLYr.imply_e(pANDq);             // line 6 ->e applied to (P ^ Q) -> R and P ^ Q
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
		// premise: Imply<Or<P, Q>, R> pqIMPLYr  // line 1
		// premise: Q q                          // line 2
		Or<P, Q> pORq = Or.or_i2(q);             // line 3 vi2 applied to Q
		R r = pqIMPLYr.imply_e(pORq);            // line 4 ->e applied to (P v Q) -> R and P v Q
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
		// premise: P p                                         // line 1
		// premise: Imply<And<Q, P>, R> qpIMPLYr                // line 2
		Deduction<Q, R> qDEDUCEr = 
				new Deduction<Q, R>(){
					public R deduction_step(Q q){
						// assumption: Q q                      // line 3
						And<Q, P> qANDp = new And<Q, P>(q, p);  // line 4 ^i  applied to Q and P
						R r = qpIMPLYr.imply_e(qANDp);          // line 5 ->e applied to (Q ^ P) -> R and Q ^ P
						return r;
					}
				};
		Imply<Q, R> qIMPLYr = new Imply<Q, R>(qDEDUCEr);        // line 6 ->i applied to deduction (... Q assume ... R)
		                                                         
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
		// premise: Imply<P, R> pIMPLYr                             // line 1 
		// premise: Imply<Q, R> qIMPLYr                             // line 2
		Deduction<Or<P, Q>, R> pqDEDUCEr = 
				new Deduction<Or<P, Q>, R>(){
					public R deduction_step(Or<P, Q> pORq){
						// assumption: P v Q                        // line 3
						Deduction<P, R> pDEDUCEr = 
								new Deduction<P, R>(){
									public R deduction_step(P p){
										// assumption: P p          // line 4
										R r = pIMPLYr.imply_e(p);   // line 5 ->e applied to P -> R and P
										return r;
									}
								};
									
						Deduction<Q, R> qDEDUCEr = 
								new Deduction<Q, R>(){
									public R deduction_step(Q q){
										// assumption: Q q          // line 6
										R r = qIMPLYr.imply_e(q);   // line 7 ->e applied to Q -> R and Q
										return r;
									}
								};
								
						R r = pORq.or_e(pDEDUCEr, qDEDUCEr);        // line 8 ve  applied to P v Q, and
						                                            //                       deduction (... P assume ... R), and 
									                                //                       deduction (... Q assume ... R)
						return r;
					}
				};
		
		Imply<Or<P, Q>, R> pqIMPLYr = new Imply<Or<P, Q>, R>(pqDEDUCEr); // line 9 ->i applied to deduction (... P V Q assume ... R)
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
		// premise: Q q                                                    // line 1
		Deduction<P, And<Q, P>> pDEDUCEqp = 
				new Deduction<P, And<Q, P>>(){
					public And<Q, P> deduction_step(P p){
						// assumption: P p                                 // line 2
						And<Q, P> qANDp = new And<Q, P>(q, p);             // line 3 ^i  applied to Q and P
						return qANDp;
					}
				};
		
		Imply<P, And<Q, P>> pIMPLYqp = new Imply<P, And<Q, P>>(pDEDUCEqp); // line 4 ->i applied to deduction (... P assume ... Q ^ P)
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
		// premise: Imply<P, Imply<Q, R>> pIMPLYqir                                  // line 1
		Deduction<Imply<P, Q>, Imply<P, R>> piqDEDUCEpir = 
				new Deduction<Imply<P, Q>, Imply<P, R>>(){
					public Imply<P, R> deduction_step(Imply<P, Q> pIMPLYq){
						// assumption: P -> Q                                        // line 2
						Deduction<P, R> pDEDUCEr = 
								new Deduction<P, R>(){
									public R deduction_step(P p){
										// assumption: P p                           // line 3
										Imply<Q, R> qIMPLYr = pIMPLYqir.imply_e(p);  // line 4 ->e applied to P -> (Q -> R) and P
										Q q = pIMPLYq.imply_e(p);                    // line 5 ->e applied to P -> Q P
										R r = qIMPLYr.imply_e(q);                    // line 6 ->e applied to Q -> R and Q
										return r;
									}
								};
						// Imply introduction
						Imply<P, R> pIMPLYr = new Imply<P, R>(pDEDUCEr);             // line 7 ->i applied to deduction (... P assume ... R)
						return pIMPLYr;
					}
				};
		
		Imply<Imply<P, Q>, Imply<P, R>> piqIMPLYpir = new Imply<Imply<P, Q>, Imply<P, R>>(piqDEDUCEpir);  // line 8 ->i applied to deduction (... P-> Q assume .... P -> R)
		return piqIMPLYpir;
	}
}




