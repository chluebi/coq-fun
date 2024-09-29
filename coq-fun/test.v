Require Setoid.

Module MyNat.
    Inductive myNat :=
        O | S (n:myNat).

    Local Notation "0" := O.
    Local Notation "1" := (S O).
    Local Notation "2" := (S (S O)).
    Local Notation "3" := (S (S (S O))).
    Local Notation "4" := (S (S (S (S O)))).
    Local Notation "5" := (S (S (S (S (S O))))).
    Local Notation "6" := (S (S (S (S (S (S O)))))).
    Local Notation "7" := (S (S (S (S (S (S (S O))))))).
    Local Notation "8" := (S (S (S (S (S (S (S (S O)))))))).
    Local Notation "9" := (S (S (S (S (S (S (S (S (S O))))))))).
    Local Notation "10" := (S (S (S (S (S (S (S (S (S (S O)))))))))).

    Create HintDb myNatDB.

    Fixpoint add (a: myNat) (b: myNat) :=
        match b with
            | O => a
            | S b' => S (add a b')
        end.

    Notation "x + y" := (add x y) (at level 50, left associativity).

    Fixpoint mul (a: myNat) (b: myNat) :=
        match b with
            | O => O
            | S b' => a + mul a b'
        end.

    Notation "x * y" := (mul x y) (at level 40, left associativity).

    Lemma addZero: forall n: myNat, n + O = n.
    Proof.
        compute.
        reflexivity.
    Qed.

    Lemma zeroAdd: forall n: myNat, O + n = n.
    Proof.
        induction n.
        - trivial.
        - simpl. rewrite IHn. reflexivity.
    Qed.


    Lemma addingIntoS: forall n m: myNat, S n + m = S (n + m).
    Proof.
        intros n m.
        induction m.
        - simpl. reflexivity.
        - simpl. rewrite IHm. reflexivity.
    Qed. 


    Lemma addCommutative: forall n m: myNat, n + m = m + n.
    Proof.
        induction m.
        - simpl. rewrite zeroAdd. reflexivity.
        - simpl. rewrite addingIntoS. rewrite IHm. reflexivity.
    Qed.


    Lemma addInjective: forall n m o: myNat, n + m = n + o -> m = o.
    Proof.
        intros n m o H.
        induction n.
        - repeat rewrite zeroAdd in H. exact H.
        - apply IHn. 
        repeat rewrite addingIntoS in H.
        injection H. intros A. apply A.
    Qed.


    Lemma addAssociative: forall n m o: myNat, n + (m + o) = (n + m) + o.
    Proof.
        intros n m o.
        induction n.
        - simpl. repeat rewrite zeroAdd. reflexivity.
        - simpl. repeat rewrite addingIntoS.
        f_equal. apply IHn.
    Qed.

    Lemma addMoveLeft: forall n m o: myNat, n + m + o = n + o + m.
    Proof.
        intros n m o.
        rewrite <- addAssociative.
        rewrite addCommutative with m o.
        rewrite addAssociative.
        reflexivity.
    Qed.


    
    Hint Resolve addZero zeroAdd addingIntoS addCommutative addInjective addAssociative addMoveLeft : myNatDB.
    Hint Rewrite addZero zeroAdd addingIntoS addCommutative addInjective addAssociative addMoveLeft : myNatDB.


    Lemma mulZero: forall n : myNat, n * 0 = 0.
    Proof.
        compute.
        reflexivity.
    Qed.

    Lemma zeroMul: forall n : myNat, 0 * n = 0.
    Proof.
        intros n.
        induction n.
        - simpl. reflexivity.
        - simpl. rewrite zeroAdd. apply IHn.
    Qed.

    Lemma mulOne: forall n : myNat, n * 1 = n.
    Proof.
        compute.
        reflexivity.
    Qed.

    Lemma OneMul: forall n: myNat, 1 * n = n.
    Proof.
        intros n.
        induction n.
        - simpl. reflexivity.
        - simpl. rewrite IHn. rewrite addCommutative. simpl. reflexivity.
    Qed.


    Lemma multIntoS0: forall n m: myNat, n * S m = n + n * m.
    Proof.
        simpl.
        reflexivity.
    Qed.


    Lemma multIntoS: forall n m: myNat, S n * m = n * m + m.
    Proof.
        induction m.
        - simpl. reflexivity.
        - simpl. rewrite addingIntoS. f_equal.
        rewrite <- addAssociative. f_equal. apply IHm.
    Qed. 


    Lemma dist: forall n m p: myNat, (m + p) * n = m * n + p * n.
    Proof.
        intros n m p.
        induction n.
        - simpl. reflexivity. 
        - simpl. rewrite <- addAssociative. rewrite <- addAssociative.
            f_equal. rewrite addAssociative.
            rewrite addCommutative with (m * n) p.
            rewrite <- addAssociative with p (m * n) (p * n).
            f_equal.
            apply IHn.
    Qed.
        

    Lemma multCommutative: forall n m: myNat, n * m = m * n.
    Proof.
        intros n m.
        induction m.
        - simpl. rewrite zeroMul. reflexivity.
        - simpl. rewrite IHm. rewrite multIntoS. rewrite addCommutative.
            reflexivity. 
    Qed.

    Lemma dist2: forall n m p: myNat, n * (m + p) = n * m + n * p.
    Proof.
        intros n m p.
        replace (n * (m + p)) with ((m + p) * n) by apply multCommutative.
        rewrite dist.
        rewrite multCommutative with m n.
        rewrite multCommutative with p n.
        reflexivity.
    Qed.

    Lemma multAssociative: forall n m o: myNat, n * (m * o) = (n * m) * o.
    Proof.
        intros n m p.
        induction n.
        - repeat rewrite zeroMul. reflexivity.
        - rewrite multIntoS. rewrite IHn. rewrite multIntoS.
            rewrite dist. reflexivity.
    Qed.

    Lemma multMoveLeft: forall n m o: myNat, n * m * o = n * o * m.
    Proof.
        intros n m p.
        rewrite <- multAssociative.
        rewrite multCommutative with m p.
        rewrite multAssociative.
        reflexivity.
    Qed.

    Hint Resolve mulZero zeroMul mulOne OneMul multIntoS0 multIntoS dist dist2 multCommutative multAssociative multMoveLeft : myNatDB.
    Hint Rewrite mulZero zeroMul mulOne OneMul multIntoS0 multIntoS dist dist2 multCommutative multAssociative multMoveLeft : myNatDB.

    Lemma timesTwo: forall n m p: myNat, 2 * n = n + n.
    Proof.
        auto with myNatDB.
    Qed.


    Fixpoint sumDownFromN (a: myNat) :=
        match a with
            | O => O
            | S a' => a + sumDownFromN a'
        end.


    Lemma gaussianSum: forall n: myNat, 2 * sumDownFromN n = n * (n + 1).
    Proof.
        intros n.
        induction n.
        - compute. reflexivity.
        - replace (2 * sumDownFromN (S n)) with (2 * (S n) + 2 * (sumDownFromN n)).
          replace (S n * (S n + 1)) with (2 * (S n) + n * (n + 1)).
          f_equal.
          apply IHn.

          replace (S n * (S n + 1)) with ((n + 1) * (n + 2)) by auto with myNatDB.
          replace (2 * S n) with (2 * (n + 1)) by auto with myNatDB.
          replace (2 * (n + 1) + n * (n + 1)) with ((2 + n) * (n + 1)) by auto with myNatDB.
          replace ((2 + n) * (n + 1)) with ((n + 1) * (2 + n)) by auto with myNatDB.
          replace (2 + n) with (n + 2) by auto with myNatDB.
          reflexivity.
        
          simpl.
          replace (2 + 2 * n) with (2 * 1 + 2 * n) by auto with myNatDB.
          replace (2 * 1 + 2 * n) with (2 * (1 + n)) by auto with myNatDB.
          replace (2 * (1 + n) + 2 * sumDownFromN n) with (2 * (1 + n + sumDownFromN n)) by auto with myNatDB.
          replace (1 + n) with (S n) by auto with myNatDB.
          reflexivity.
    Qed.


    Fixpoint pow (a: myNat) (b: myNat) :=
        match b with
            | O => 1
            | S b' => a * (pow a b')
        end.

    Lemma zeroPower: forall n : myNat, (n = O /\ pow 0 n = 1) \/ (n <> 0 /\ pow 0 n = 0).
    Proof.
        destruct n.
            + compute. left. split. reflexivity. reflexivity.
            + right. split. discriminate.
            simpl. apply zeroMul.
    Qed.

    Lemma onePower: forall n : myNat, pow 1 n = 1.
    Proof.
        induction n.
        - compute. reflexivity.
        - simpl. rewrite OneMul. apply IHn.
    Qed.

    Fixpoint powerSumDownFromN (a: myNat) (p: myNat) :=
    match a with
        | O => O
        | S a' => pow a p + powerSumDownFromN a' p
    end.

    Lemma powerGaussianSum: forall n: myNat, 6 * powerSumDownFromN n 2 = n * (n + 1) * (2 * n + 1).
    Proof.
        induction n.
        - compute. reflexivity.
        - simpl.
        replace (6 * (S n + S n * n + powerSumDownFromN n 2)) 
        with (6 * (S n + S n * n) + 6 * powerSumDownFromN n 2) by auto with myNatDB.
        rewrite dist2 with 6 (S n) (S n * n).
        
        replace (S n + (S n + S n * n)) with (S n + S n + S n * n) by auto with myNatDB.
        replace (2 + 2 * n) with (1 + (2 * n + 1)) by auto with myNatDB.
        rewrite dist2 with (S n + S n + S n * n) 1 (2 * n + 1).
        rewrite dist with (2 * n + 1) (S n + S n) (S n * n).
        replace (S n * n * (2 * n + 1)) with ((n + 1) * n  * (2 * n + 1)) by auto with myNatDB.
        rewrite multCommutative with (n + 1) n.
        rewrite IHn.
        rewrite addAssociative.
        rewrite addAssociative.
        rewrite mulOne.
        replace ((S n + S n) * (2 * n + 1)) with ((S n + S n) * (2 * n) + (S n + S n)) by auto with myNatDB.
        replace (S n + S n) with (2 * (S n)) by auto with myNatDB.
        replace (2 * (S n) * (2 * n)) with (2 * (S n) * 2 * n) by auto with myNatDB.
        replace (2 * (S n) * 2) with (2 * 2 * (S n)) by auto with myNatDB.
        replace (2 * 2) with 4 by auto with myNatDB.
        rewrite addAssociative.
        rewrite addAssociative.
        replace (2 * S n + S n * n + 2 * S n) with (2 * S n + 2 * S n + S n * n) by auto with myNatDB.
        replace (2 * S n + 2 * S n) with ((2 + 2) * S n) by auto with myNatDB.
        replace (2 + 2) with 4 by auto with myNatDB.
        replace (4 * S n + S n * n + S n * n) with (4 * S n + (S n * n + S n * n)) by auto with myNatDB.
        replace (S n * n + S n * n) with (2 * (S n * n)) by auto with myNatDB.
        replace (4 * S n * n) with (4 * (S n * n)) by auto with myNatDB.
        replace (4 * S n + 2 * (S n * n) + 4 * (S n * n)) with (4 * S n + (2 * (S n * n) + 4 * (S n * n))) by auto with myNatDB.
        replace ((2 * (S n * n) + 4 * (S n * n))) with ((2 + 4) * (S n * n)) by auto with myNatDB.
        replace (2 + 4) with 6 by auto with myNatDB.
        replace (4 * S n + 6 * (S n * n) + 2 * S n) with (4 * S n  + 2 * S n + 6 * (S n * n)) by auto with myNatDB.
        replace (4 * S n  + 2 * S n) with ((4 + 2) * S n) by auto with myNatDB.
        replace (4 + 2) with 6 by auto with myNatDB.
        reflexivity.
    Qed.

End MyNat.

Export MyNat.

