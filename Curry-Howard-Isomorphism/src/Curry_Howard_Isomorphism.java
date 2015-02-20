
public class Curry_Howard_Isomorphism {
	public class P{}
	
	public class Q{}
	
	public class R{}
	
	/**
	 * To illustrate the relationship between proofs and programs, as described by Curry–Howard isomorphism, 
	 * we introduce the following judgment:
	 *  V: T         V is a proof term (evidence) for proposition T, which can also be interpreted as
	 *  V: T         V is an object of type T
	 *  
	 *  These dual interpretations of the same judgment are the core of the Curry-Howard isomorphism 
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
		 * The 'And' introduction rule can be thought of as a program step or a method that
                 * takes a value of type T1 and T2 respectively
		 * and produces a value of type And<T1, T2>;  We can represent the introduction
                 * rule as a constructor for a parametric class And<T1,T2>
		 * 
		 * by Curry-Howard isomorphism, if T1 and T2 are propositions, then the constructor
                 * can be interpreted as taking evidence of the truth 
		 * of propositions T1 and T2 respectively and producing evidence of the truth of proposition
                 *  And<T1, T2> (i.e., T1 ^ T2).
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
		 * 'end_e1' can be thought of as a program step or method that takes an value of type And<T1, T2> returns a value of type T1;
                 * Note that the 'this' variable represents the implicit input (of type And<T1, T2>) to this method.
		 * 
		 * by Curry-Howard isomorphism, if T1 and T2 are propositions, then it can be interpreted as taking evidence of the truth of 
		 * proposition And<T1, T2> (i.e., T1 ^ T2) and producing a evidence of the truth of T1.
		 * This corresponds to And-elimination rule ^e1:
		 * 
		 *  T1 ^ T2
		 *  ------- (^e1)
		 *    T1
		 **/
		public T1 and_e1(){
			return v1;
		}
		
		
		/**
		 * 'end_e2' can be thought of as a program step or method that takes an value of type And<T1, T2> returns a value of type T2;
                 * Note that the 'this' variable represents the implicit input (of type And<T1, T2>) to this method.
		 * 
		 * by Curry-Howard isomorphism, if T1 and T2 are propositions, then it can be interpreted as taking evidence of the truth of 
		 * proposition And<T1, T2> (i.e., T1 ^ T2) and producing evidence of the truth of T2.
		 * This corresponds to And-elimination rule ^e2:
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
	 * for any types T1 and T2, we want instances of the class Or<T1,T2> to provide evidence of
         * the proposition T1 v T2.  To achieve this, note that if T1 v T2 is true, our evidence
         * needs to indicate *which* of T1 or T2 is true.  There are a number of ways to achieve
         * this. E.g., One could have two fields for both T1 and T2 and in And, and introduce some sort of flag 
         * indicating which field represented the evidence.  However, we do it in way that is a bit
         * cleaner.  We create two subclasses of Or<T1,T2> -- one representing the case where T1 is true,
         * the other representing the case where T2 is true.  Then, when we need to do "or elimination",
         * we can use "instance of" to check which one is true.
         *
         * Below is some other technical stuff for people interested in functional programming.
         * [You don't need to understand the rest of the comment.]
         *
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
		
		private T1 left() { return null; }
		private T2 right() { return null; }
		
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
		 * The 'Or' introduction rule "vi1" can be thought of as a program step or a method that
                 * takes a value of type T1 respectively
		 * and produces a value of type Or<T1, T2>;  In the implementation of the 
                 * method, we use the constructor for the subclass "Left" to create the value, 
                 * which has the effect of "tagging" the object so that we know the "left side" of T1 v T2 
                 * is true.
		 * 
		 * by Curry-Howard isomorphism, if T1 and T2 are propositions, then the method
                 * can be interpreted as taking evidence of the truth 
		 * of propositions T2 and producing evidence of the truth of proposition
                 *  Or<T1, T2> (i.e., T1 v T2).
                 *
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
		 * The 'Or' introduction rule "vi2" can be thought of as a program step or a method that
                 * takes a value of type T1 respectively
		 * and produces a value of type Or<T1, T2>;  In the implementation of the 
                 * method, we use the constructor for the subclass "Right" to create the value, 
                 * which has the effect of "tagging" the object so that we know the "right side" of T1 v T2 
                 * is true.
		 * 
		 * by Curry-Howard isomorphism, if T1 and T2 are propositions, then the method
                 * can be interpreted as taking evidence of the truth 
		 * of proposition T2 and producing evidence of the truth of proposition
                 *  Or<T1, T2> (i.e., T1 v T2).
                 *
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
                 * The 'Or' elimination rule uses the Deduction class below, so read the documentation
                 * for that class first.
                 *
                 * The 'Or' elimination rule can be though of as a program step or a method 'or_e' that
                 * takes three inputs...
                 *  (1) a value of Or<T1,T2> (the implicit 'this' variable) 
                 *  (2) a Deduction object containing a method that transforms values of T1 into values of T3
                 *  (3) a Deduction object containing a method that transforms values of T2 into values of T3
                 * ...and produces a value of type T3.
                 *
                 * 'or_e' works by checking to see whether the class of 'this' is Left or Right and then
                 * calling either the "getter" method left() or right() as appropriate.  If the class of this
                 * is "Left" the subproof that proves T3 given T1 is activated to return an object of type T3.
                 * If the class of this is "Right" the subproof that proves T3 given T2 
                 * is activated to return an object of type T3.
                 
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
	/**        Representing a "sub-proof" i.e., a set of proof steps 
        /**        that is "boxed" is our proof checker
	/*****************************************************************/		

        /**
	 * Several of our proof rules use sub-proofs that look like this...
         *
         *      ... T1  assumption
         *      ...
         *      ... T2
         *
         * We can think of such a sub-proof as a method that, if given evidence for
         * T1 can produce evidence for T2.
         *
         * We create a special class to wrap this type of method.
         * The class is Deduction<T1,T2> and objects of the class have a method called
         * 'deduction_step' that essentially represents
         * a proof of the sequent T1 |- T2.
         * 
         * In the programming world, whenever we want to create a proof of T1 |- T2, 
         * we create an instance of Deduction<T1,T2> and override the deduction_step 
         * method with a method representing a proof of T1 |- T2.
         *
	 * We also create a method called "apply", intuitively, that "activates" the
         * subproof to by giving it evidence for T1 which will cause it to produce
         * evidence for T2.
	 **/

	public abstract class Deduction<T1, T2>{

                /**
		 * Override this method to represent a subproof that takes evidence of
                 * an assumption T1 and produces evidences for T2.
		 * 
                 **/
		public abstract T2 deduction_step(T1 assumptions);
		
                /**
		 * Use this method to "activate" a subproof -- if evidence of
                 * an assumption T1 is given, it will produce evidences for T2.
		 * 
                 **/
		public T2 apply(T1 v1){
			return deduction_step(v1);
		}
	}
	

	/*****************************************************************/
	/**        Implies-introduction and Implies-elimination          */
	/*****************************************************************/		
	
	public class Imply<T1, T2>{
		private Deduction<T1, T2> deduction;
		
		/**
                 * The 'Implies' introduction rule can be thought of as a program step or a method that
                 * takes as input an object encapsulating a deduction (i.e., a method) that provides
                 * way to transform a value of type T1 into a value of type T2 and produces an object of type
                 * Implies<T1,T2>.  We can represent the introduction
                 * rule as a constructor for a parametric class Implies<T1,T2>
		 * 
		 * by Curry-Howard isomorphism, then the constructor can be interpreted as taking 
                 * a subproof that, given evidence of the truth of propositions T1 can
                 * produce evidence of the truth of proposition T2.  In our representation, a subproof
                 * (the stuff above the bar in the ->i rule) is represented as an object of the
                 * Deduction class.  The Deduction class object contains a method deduction_step
                 * that takes as input evidence for the truth of T1 and produces evidence of the truth
                 * of T2.   Thus, evidence for the truth of the proposition T1 -> T2 is a method
                 * (aka procedure, subroutine) for transforming T1 evidence into T2 evidence.
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
		 * 'imply_e' can be thought of as a program step or method that takes an object of type Implies<T1, T2> and an object of 
                 * type T1 and returns an object of type T2;
                 * Note that the 'this' variable represents the implicit input (of type Imply<T1, T2>) to this method.
		 * 
		 * by Curry-Howard isomorphism, if T1 and T2 are propositions, then it can be interpreted as taking evidence of the truth of 
		 * proposition Imply<T1, T2> (i.e., T1 -> T2), evidence of the truth of T1, and producing a evidence of the truth of T2.
                 * Intuitively, the evidence for T2 is constructed by using the evidence for T1 -> T2.  Specificly, the evidence
                 * for T1 -> T2 is a method deduction_step (wrapped inside of a Deduction object) that transforms T1 evidence into
                 * T2 evidence.  Because we have evidence for T1 (the argument v of the method), we can apply the T1 -> T2 evidence
                 * (i.e., the deduction_step procedure) to the T1 evidence to get the T2 evidence.
                 *
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

	/** =========================================
	 *   S u m m a r y
         *
         *     For any propositional variable P, Q, R, whenever the propositional variable is true, we assume
         *     that there is some way of representing evidence of the truth of the propositional variable.
         * 
         *     For any non-primitive proposition built with the connectives ^, v, and ^, we can 
         *     represent evidence of the truth of that proposition using Java objects.
         *     
         *     Evidence for T1 ^ T2  is an object with two fields: one holding evidence of T1 and the 
         *     other holding evidence of T2
         *
         *     Evidence for T1 v T2  is an object with a tag indicating that which of T1 or T2 is true.
         *     In our case, the "tag" is represented by the run-time type of a T1 v T2 object
         *     (which is either a Left object or a Right object).  We check the tag by performing
         *     an "instance of" operation on the T1 v T2 (i.e., Or<T1,T2>) object.
         *     If the tag indicates that T1 is true, then the evidence object for T1 v T2 includes
         *     evidence of T1.  If T2 is true, then the evidence object for T1 v T2 includes evidence of T2.
         *
         *     Evidence for T1 v T2  is an object with a tag indicating that which of T1 or T2 is true.
         *     In our case, the "tag" is represented by the run-time type of a T1 v T2 object
         *     (which is either a Left object or a Right object).  We check the tag by performing
         *     an "instance of" operation on the T1 v T2 (i.e., Or<T1,T2>) object.
         *     If the tag indicates that T1 is true, then the evidence object for T1 v T2 includes
         *     evidence of T1.  If T2 is true, then the evidence object for T1 v T2 includes evidence of T2.
	 *
	 **/

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




