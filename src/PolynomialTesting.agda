module _ where

data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

_+_ : (x y : Nat) -> Nat
ze + y = y
su x + y = su (x + y)
infix 5 _+_

_×_ : (n x : Nat) -> Nat
ze × x = ze
su n × x = (n × x) + x
infix 6 _×_

_^_ : (x n : Nat) -> Nat
x ^ ze = 1
x ^ su n = (x ^ n) × x

data _≡_ {A : Set} (a : A) : A -> Set where
  refl : a ≡ a
infix 0 _≡_

data Add : (l m n : Nat) -> Set where
  zel : ∀ {n} -> Add ze n n
  zer : ∀ {n} -> Add n ze n
  susu : ∀ {l m n} -> Add l m n -> Add (su l) (su m) (su (su n))

data Poly : Nat -> Set where
  κ : ∀ {n} -> Nat -> Poly n
  ι : ∀ {n} -> Poly (su n)
  ↑ : ∀ {n} -> Poly n -> Poly n
  _⊕_ : ∀ {n} -> Poly n -> Poly n -> Poly n
  times : ∀ {l m n} -> Poly l -> Poly m -> Add l m n -> Poly n
infixr 5 _⊕_

⟦_⟧ : ∀ {n} -> Poly n -> Nat -> Nat
⟦ κ n ⟧ x = n
⟦ ι ⟧ x = x
⟦ ↑ p ⟧ x = ⟦ p ⟧ (su x)
⟦ p ⊕ r ⟧ x = ⟦ p ⟧ x + ⟦ r ⟧ x
⟦ times p r a ⟧ x = ⟦ p ⟧ x × ⟦ r ⟧ x


sul : ∀ {l m n} -> Add l m n -> Add (su l) m (su n)
sul (zel {ze}) = zer
sul (zel {su n}) = susu zel
sul zer = zer
sul (susu s) = susu (sul s)

sur : ∀ {l m n} -> Add l m n -> Add l (su m) (su n)
sur zel = zel
sur (zer {ze}) = zel
sur (zer {su n}) = susu zer
sur (susu s) = susu (sur s)

Δ : ∀ {n} -> Poly (su n) -> Poly n
Δ (κ _) = κ 0
Δ ι = κ 1
Δ (↑ p) = ↑ (Δ p)
Δ (p ⊕ r) = Δ p ⊕ Δ r
Δ (times p r zel) = times (κ (⟦ p ⟧ 0)) (Δ r) zel
Δ (times p r zer) = times (Δ p) (κ (⟦ r ⟧ 0)) zer
Δ (times p r (susu a)) = times (Δ p) (↑ r) (sur a) ⊕ times p (Δ r) (sul a)

add : (l m : Nat) -> Add l m (l + m)
add ze m = zel
add (su l) m = sul (add l m)

_⊗_ : ∀ {l m} -> Poly l -> Poly m -> Poly (l + m)
_⊗_ {l} {m} p r = times p r (add l m)
infixr 6 _⊗_

ι₁ : Poly 1
ι₁ = ι

κ₀ : Nat -> Poly 0
κ₀ n = κ n

_o^_ : ∀ {m} -> Poly m -> (n : Nat) -> Poly (n × m)
p o^ ze = κ 1
p o^ su n = (p o^ n) ⊗ p

ex-poly2 : Poly 2
ex-poly2 = (ι₁ o^ 2) ⊕ κ₀ 2 ⊗ ι ⊕ κ 1
