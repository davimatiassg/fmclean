
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro h,
  intro g,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  by_cases h: P,
  {intro g,
  exact h,
  },
  {intro g,
  have q:= g h,
  contradiction,}
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  have k := doubleneg_elim P,
  exact k,
  have k := doubleneg_intro P,
  exact k,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro h,
  cases h with hp hq,
  right,
  assumption,
  left,
  assumption,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro h,
  cases h with hp hq,
  split,
  exact hq,
  exact hp,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro h,
  intro p,
  cases h with hnp hq,
  contradiction,
  exact hq,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro h,
  intro np,
  cases h with p q,
  contradiction,
  exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro h,
  intro nq,
  intro p,
  have q := h p,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro h,
  intro p,
  by_cases lemQ: Q,
  exact lemQ,
  have np := h lemQ,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  have k := impl_as_contrapositive P Q,
  exact k,
  have k := impl_as_contrapositive_converse P Q,
  exact k,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro nLEM,
  have LEM : P ∨ ¬P,
    right,
    intro p,
    have re_LEM : P ∨ ¬P,
      left,
      exact p,
      contradiction,
  contradiction,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro h,
  intro np,
  have h_contraposer := impl_as_contrapositive (P → Q) P,
  have contrapos_h := h_contraposer h,
  have n_ptoq := contrapos_h np,
  have ptoq : P → Q,
    intro p,
    contradiction,
  contradiction,
end

-------------------
-- Estou ciente de que o jeito acima é mais trabalhoso do que o ideal. Fiz-lhe assim e assim manter-lhe-ei por fins científicos somente.
-------------------

------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro porq,
  intro npnq,
  cases npnq with np nq,
  cases porq with p q,
  contradiction,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro pq,
  intro npRnq,
  cases pq with p q,
  cases npRnq with np nq,
  contradiction,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro npRq,
  split,
  intro p,
  have pRq : P ∨ Q,
    left,
    exact p,
  contradiction,
  intro q,
  have pRq : P ∨ Q,
    right,
    exact q,
  contradiction,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro npnq,
  intro pRq,
  cases npnq with np nq,
  cases pRq with p q,
    contradiction,
    contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro npq,
  by_cases lemp : P,
  left,
  by_contradiction nnq,
  have cont :P∧Q,
    split,
    exact lemp,
    exact nnq,
  contradiction,
  right,
  exact lemp,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro nqRnp,
  intro pq,
  cases pq with p q,
  cases nqRnp with nq np,
    contradiction,
    contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  have k := demorgan_conj P Q,
  exact k,
  have k := demorgan_conj_converse P Q,
  exact k,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  have k := demorgan_disj P Q,
  exact k,
  have k := demorgan_disj_converse P Q,
  exact k,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro pqRr,
  cases pqRr with p qRr,
  cases qRr with q r,
  left,
  have pq : P ∧ Q,
    split,
    exact p,
    exact q,
  exact pq,
  right,
  have pr : P ∧ R,
    split,
    exact p,
    exact r,
  exact pr,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro pqRpr,
  cases pqRpr with pq pr,
    cases pq with p q,
    split,
    exact p,
    left,
    exact q,
    cases pr with p r,
    split,
    exact p,
    right,
    exact r,
  
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro pRqr,
  cases pRqr with p qr,
  split,
  left,
  exact p,
  left,
  exact p,
  cases qr with q r,
  split,
  right,
  exact q,
  right,
  exact r,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro pRqpRr,
  cases pRqpRr with pRq pRr,
  cases pRq with p q,
  left,
  exact p,
  cases pRr with p r,
  left,
  exact p,
  right,
  have qr : Q∧R,
    split,
    exact q,
    exact r,
  exact qr,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro pqTr,
  intro p,
  intro q,
  have pq : P∧Q,
    split,
    exact p,
    exact q,
  have r := pqTr pq,
  exact r,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro pTqTr,
  intro pq,
  cases pq with p q,
  have qTr := pTqTr p,
  have r := qTr q,
  exact r,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pq,
  cases pq with p q,
  exact p,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,
  cases pq with p q,
  exact q,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro pp,
  cases pp with p1 p2,
  exact p1,
  intro p,
  split,
  exact p,
  exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro pRp,
  cases pRp with p1 p2,
  exact p1,
  exact p2,
  intro p,
  left,
  exact p,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro nEpx,
  intro x,
  intro px,
  have cont : (∃x, P x),
    existsi x,
    exact px,
  contradiction,
    
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro xp,
  intro nxp,
  cases nxp with x,
  have cont := xp x,
  contradiction,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  apply impl_as_contrapositive_converse  (¬(∀x, P x)) (∃x, ¬P x),
  intro nEnpx,
  apply doubleneg_intro (∀x, P x),
  intro x,
  by_contra,
  have Enpx : ∃x, ¬P x,
    existsi x,
    exact h,
  contradiction,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro Exnpx,
  intro Fxpx,
  cases Exnpx with x npx,
  have px := Fxpx x,
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  have k := demorgan_forall U P,
  exact k,
  have k := demorgan_forall_converse U P,
  exact k,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  have k := demorgan_exists U P,
  exact k,
  have k := demorgan_exists_converse U P,
  exact k,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro Epx,
  intro nFnpx,
  cases Epx with x px,
  have npx := nFnpx x,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
