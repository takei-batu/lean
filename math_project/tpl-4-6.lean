-- 1.
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
⟨
  fun h => ⟨ fun t => (h t).left , fun t => (h t).right ⟩,
  fun ⟨h₁ , h₂⟩ => fun t => ⟨h₁ t , h₂ t⟩
⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h g => fun t => (h t) (g t)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h => Or.elim h (fun h₁ => fun t => Or.inl (h₁ t)) (fun h₂ => fun t => Or.inr (h₂ t))

-- 2.
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _ : α, r) ↔ r) := fun t =>
⟨
  fun h => h t,
  fun h => fun _ => h
⟩

open Classical
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
⟨
  fun h =>  Or.elim (em r)
    (fun hr => Or.inr hr)
    (fun hnr => Or.inl (fun t => Or.elim (h t)
      (fun hpt => hpt)
      (fun hr => absurd hr hnr)
    )),
  fun h => Or.elim h (fun h₁ => fun t => Or.inl (h₁ t)) (fun h₂ => fun _ => Or.inr h₂)
⟩

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
⟨
  fun h => fun hr => fun t => (h t) hr,
  fun h =>  fun t => fun hr => (h hr) t
⟩

-- 3.
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop) -- men1 は men2 の髭を剃る

-- barber は自分自身で髭を剃らない人の髭を剃る
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have ⟨ hbr , hbl ⟩ : shaves barber barber ↔ ¬ shaves barber barber := ⟨(h barber).mp, (h barber).mpr⟩
  show False from Or.elim (em (shaves barber barber)) (fun g => (hbr g) g) (fun g => g (hbl g))

-- 4.
def divides (x y : Nat) : Prop := ∃ k, k * x = y

def even (n : Nat) : Prop := ∃ x : Nat, n = 2 * x

def prime (n : Nat) : Prop := n > 1 ∧ ∀ a : Nat, divides a n → a = 1 ∨ a = n

def infinitely_many_primes : Prop := ∀ p : Nat, ∃ q : Nat, prime q ∧ p < q

def Fermat_prime (n : Nat) : Prop := prime n ∧ ∃ k : Nat, n = 2 ^ (2 ^ k) + 1

def infinitely_many_Fermat_primes : Prop := ∀ p : Nat, Fermat_prime p → ∃ q : Nat, Fermat_prime q ∧ p < q

def goldbach_conjecture : Prop := ∀ n : Nat, n ≥ 4 ∧ even n → ∃ p₁ p₂ : Nat, n = p₁ + p₂ ∧ prime p₁ ∧ prime p₂

def Goldbach's_weak_conjecture : Prop := ∀ n : Nat, n > 5 ∧ ¬ even n → ∃ p₁ p₂ p₃ : Nat, n = p₁ + p₂ ∧ prime p₁ ∧ prime p₂ ∧ prime p₃

def Fermat's_last_theorem : Prop := ∀ n : Nat, n ≥ 3 → ¬ ∃ x y z : Nat, x ^ n + y ^n = z ^n
