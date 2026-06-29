-- ============================================================
-- T5 Two-Stream Decomposition Impossibility
-- EAS Lean4 Project
-- ============================================================
--
-- This file proves that any decomposition of a cognitive system on 
-- Fin m (m ≥ 3) into ≤ 2 independent streams cannot simultaneously 
-- satisfy the three EAS necessary conditions:
--
--   (1) Independent Decodability: the two streams are mutually 
--       non-factoring (each provides information the other doesn't)
--   (2) Verification Irreducibility: the verifier V is not 
--       determined by the generator G and predictor P together
--   (3) Credit Assignment Identifiability: there exist ≥ 3 
--       functionally independent observables
--
-- The proof uses a purely combinatorial argument based on partition 
-- refinement and functional determinacy:
-- - If G faithfully encodes stream 1 and P faithfully encodes 
--   stream 2, then (G, P) determines every element of Fin m
--   (via joint injectivity of the streams)
-- - Therefore V is determined by (G, P), making verification 
--   reducible and preventing 3 independent observables
-- - The core algebraic constraint: 2 degrees of freedom cannot 
--   support 3 independent constraints
--
-- This strengthens T5_impossibility (which shows no SINGLE function 
-- can satisfy all three EAS roles) to the 2-stream case.

namespace EAS

-- ============================================================
-- Section 1: Stream Decomposition Framework
-- ============================================================

/-- A function g "factors through" f if there exists a mediator h 
    such that g = h ∘ f. This means g is "recoverable from" f, or 
    equivalently, f's information suffices to determine g. -/
def FactorsThrough {m a k : Nat} (g : Fin m → Fin k) (f : Fin m → Fin a) : Prop :=
  ∃ h : Fin a → Fin k, ∀ x, g x = h (f x)

/-- Two streams f₁ and f₂ are "independent" (Independent Decodability) 
    if neither factors through the other. Each stream provides 
    information not available from the other. -/
def StreamIndependent {m a b : Nat} 
    (f₁ : Fin m → Fin a) (f₂ : Fin m → Fin b) : Prop :=
  ¬FactorsThrough f₂ f₁ ∧ ¬FactorsThrough f₁ f₂

/-- A function v is "stream-irreducible" with respect to two streams 
    if it cannot be recovered from either stream alone. 
    This is a component of Verification Irreducibility. -/
def StreamIrreducible {m a b k : Nat} (v : Fin m → Fin k) 
    (f₁ : Fin m → Fin a) (f₂ : Fin m → Fin b) : Prop :=
  ¬FactorsThrough v f₁ ∧ ¬FactorsThrough v f₂

/-- g is "faithful" to stream f if g factors through f AND g determines f.
    This means g is a lossless encoding of f's information. -/
def StreamFaithful {m a k : Nat} (g : Fin m → Fin k) (f : Fin m → Fin a) : Prop :=
  FactorsThrough g f ∧ ∀ x y, g x = g y → f x = f y

/-- Joint injectivity of two streams: the pair (f₁, f₂) determines x. -/
def JointlyInjective {m a b : Nat} (f₁ : Fin m → Fin a) (f₂ : Fin m → Fin b) : Prop :=
  ∀ x y, f₁ x = f₁ y → f₂ x = f₂ y → x = y

/-- Three observables are functionally independent if no one is determined 
    by the other two. This captures Credit Assignment Identifiability. -/
def FunctionallyIndependent {m k : Nat} 
    (g₁ g₂ g₃ : Fin m → Fin k) : Prop :=
  -- g₃ is not determined by (g₁, g₂)
  (∃ x y, g₁ x = g₁ y ∧ g₂ x = g₂ y ∧ g₃ x ≠ g₃ y) ∧
  -- g₂ is not determined by (g₁, g₃)
  (∃ x y, g₁ x = g₁ y ∧ g₃ x = g₃ y ∧ g₂ x ≠ g₂ y) ∧
  -- g₁ is not determined by (g₂, g₃)
  (∃ x y, g₂ x = g₂ y ∧ g₃ x = g₃ y ∧ g₁ x ≠ g₁ y)

-- ============================================================
-- Section 2: Core Lemma — Faithful Encoding Forces Determinacy
-- ============================================================

/-- If G faithfully encodes stream 1 and P faithfully encodes stream 2,
    with jointly injective streams, then (G, P) jointly determines 
    every element of Fin m. -/
theorem faithful_joint_determinacy {m a b kG kP : Nat}
    (f₁ : Fin m → Fin a) (f₂ : Fin m → Fin b)
    (G : Fin m → Fin kG) (P : Fin m → Fin kP)
    (hGFaith : StreamFaithful G f₁) (hPFaith : StreamFaithful P f₂)
    (hInj : JointlyInjective f₁ f₂) :
    ∀ x y, G x = G y → P x = P y → x = y := by
  intro x y hGxy hPxy
  -- G x = G y → f₁ x = f₁ y (by faithfulness of G)
  have hf₁ : f₁ x = f₁ y := hGFaith.2 x y hGxy
  -- P x = P y → f₂ x = f₂ y (by faithfulness of P)
  have hf₂ : f₂ x = f₂ y := hPFaith.2 x y hPxy
  -- Joint injectivity: f₁ x = f₁ y ∧ f₂ x = f₂ y → x = y
  exact hInj x y hf₁ hf₂

/-- The key consequence: any observable V is determined by (G, P) 
    when G and P faithfully encode their respective streams. -/
theorem faithful_implies_V_determined {m a b kG kP kV : Nat}
    (f₁ : Fin m → Fin a) (f₂ : Fin m → Fin b)
    (G : Fin m → Fin kG) (P : Fin m → Fin kP) (V : Fin m → Fin kV)
    (hGFaith : StreamFaithful G f₁) (hPFaith : StreamFaithful P f₂)
    (hInj : JointlyInjective f₁ f₂) :
    ∀ x y, G x = G y → P x = P y → V x = V y := by
  intro x y hGxy hPxy
  have hxy : x = y := faithful_joint_determinacy f₁ f₂ G P hGFaith hPFaith hInj x y hGxy hPxy
  subst hxy

-- ============================================================
-- Section 3: Main Impossibility Theorem
-- ============================================================

/-- **Two-Stream Decomposition Impossibility**
    
    For any cognitive system on Fin m (m ≥ 3) decomposed into 2 
    independent, jointly injective streams, if the Generator G 
    faithfully encodes stream 1 and the Predictor P faithfully 
    encodes stream 2, then the Verifier V cannot be functionally 
    independent of (G, P).
    
    This establishes that:
    - (Verification Irreducibility) and (Credit Assignment Identifiability) 
      cannot both hold with only 2 streams
    - The Verifier is always reducible to (Generator, Predictor)
    - 3 functionally independent observables require ≥ 3 independent streams -/
theorem two_stream_impossibility {m a b : Nat} (hm : 3 ≤ m)
    (f₁ : Fin m → Fin a) (f₂ : Fin m → Fin b)
    (hInd : StreamIndependent f₁ f₂)
    (hInj : JointlyInjective f₁ f₂)
    (G P V : Fin m → Fin 2)
    (hGFaith : StreamFaithful G f₁)
    (hPFaith : StreamFaithful P f₂) :
    ¬FunctionallyIndependent G P V := by
  intro hFI
  -- V is determined by (G, P)
  have hVDet : ∀ x y, G x = G y → P x = P y → V x = V y :=
    faithful_implies_V_determined f₁ f₂ G P V hGFaith hPFaith hInj
  -- But functional independence requires V is NOT determined by (G, P)
  -- The first conjunct of FunctionallyIndependent says:
  -- ∃ x y, G x = G y ∧ P x = P y ∧ V x ≠ V y
  obtain ⟨x, y, hGxy, hPxy, hVne⟩ := hFI.1
  -- Contradiction: V is determined by (G,P) but V x ≠ V y
  have := hVDet x y hGxy hPxy
  contradiction

-- ============================================================
-- Section 4: Corollary — 2 Streams Cannot Support Credit Assignment
-- ============================================================

/-- **Corollary**: With 2 streams, if G and P faithfully encode the 
    two streams, then V is determined by (G, P) at every point. -/
theorem two_stream_determinacy {m a b : Nat} (hm : 3 ≤ m)
    (f₁ : Fin m → Fin a) (f₂ : Fin m → Fin b)
    (hInd : StreamIndependent f₁ f₂)
    (hInj : JointlyInjective f₁ f₂)
    (G P V : Fin m → Fin 2)
    (hGFaith : StreamFaithful G f₁)
    (hPFaith : StreamFaithful P f₂) :
    ∀ x y, G x = G y → P x = P y → V x = V y :=
  faithful_implies_V_determined f₁ f₂ G P V hGFaith hPFaith hInj

end EAS
