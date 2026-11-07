using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class JenzerPermutedRotorLoopAlgebraDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/JenzerPermutedRotorLoopAlgebra.";
    private const string Note = "D5/L/QuadraticForms/jenzer2026starorderedrotorloops";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native scalar traces and ordered Clifford products.", H("JenzerPermutedRotorLoopAlgebra"),
        Blocks(
            Describe.Lean(DescribeId.Create("scalarprojection"), DeclarationHandle.Create(Prefix + "scalarProjection"), H("Native scalar coefficient"),
                StatementSource.FromAuthor(Disp(Formula0())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Definition D2.1, page 8: “For "), Math(Seq(X("x"), Sp, Eq, Sp, new Formula.Subscript(Sum, X("A")), Sp, new Formula.Subscript(X("x"), X("A")), Sp, new Formula.Subscript(X("e"), X("A")), Sp, InMacro, Sp, Seq(Mathcal, Sp, Grp(X("C"))))), Text(", "), Math(Seq(new Formula.Subscript(Seq(Langle, Sp, X("x"), Sp, Rangle), D(0)), Sp, Colon, Sp, Eq, Sp, new Formula.Subscript(X("x"), Emptyset), Sp, InMacro, Sp, Real)), Text(" is called the scalar part of "), Math(X("x")), Text("; the map "), Math(Seq(new Formula.Subscript(Seq(Langle, Sp, Cdot, Sp, Rangle), D(0)), Sp, Colon, Sp, Seq(Mathcal, Sp, Grp(X("C"))), Sp, To, Sp, Real)), Text(" is the scalar projection or grade-0 projection. It is linear.” The linear Clifford-to-exterior equivalence reads this coefficient; multiplication is the Clifford product."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("isbivector"), DeclarationHandle.Create(Prefix + "IsBivector"), H("Homogeneous bivectors"),
                StatementSource.FromAuthor(Disp(Formula1())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Section 2.1, page 8: “We call "), Math(new Formula.Subscript(X("e"), X("A"))), Text(" a basis blade of grade "), Math(Seq(X("r"), Sp, Eq, Sp, Lvert, Sp, X("A"), Sp, Rvert)), Text(".” A bivector belongs to the homogeneous exterior power of degree two under the linear exterior equivalence."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("anticommutingunitfamily"), DeclarationHandle.Create(Prefix + "AnticommutingUnitFamily"), H("Anticommuting unit bivectors"),
                StatementSource.FromAuthor(Disp(Formula2())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Definition D3.2, page 10: “A family B₁, …, Bₖ of bivectors of a real Clifford algebra is called an anticommuting unit family of type −1 if Bᵢ² = −1 (1 ≤ i ≤ k), BᵢBⱼ = −BⱼBᵢ (i ≠ j).” The source set is represented by Fin k through the increasing map i ↦ i + 1."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("subsetproduct"), DeclarationHandle.Create(Prefix + "subsetProduct"), H("Increasing subset product"),
                StatementSource.FromAuthor(Disp(Formula3())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Definition D2.4, page 9: “Let "), Math(Seq(Seq(new Formula.Subscript(X("B"), D(1)), Sp, Comma, Sp, Sp, Sp, Seq(Dot, Dot, Dot), Sp, Comma, Sp, Sp, Sp, new Formula.Subscript(X("B"), X("k"))), Sp, InMacro, Sp, Seq(Mathcal, Sp, Grp(X("C"))))), Text(" be given. For "), Math(Seq(X("S"), Sp, Eq, Sp, OpenBrace, Sp, new Formula.Subscript(X("i"), D(1)), Sp, Lt, Sp, new Formula.Subscript(X("i"), D(2)), Sp, Lt, Sp, Seq(Cdot, Cdot, Cdot), Sp, Lt, Sp, new Formula.Subscript(X("i"), X("m")), Sp, CloseBrace, Sp, Subseteq, Sp, OpenBrace, Sp, D(1), Sp, Comma, Sp, Seq(Dot, Dot, Dot), Sp, Comma, Sp, X("k"), Sp, CloseBrace)), Text(" we set "), Math(Seq(new Formula.Subscript(X("B"), X("S")), Sp, Colon, Sp, Eq, Sp, new Formula.Subscript(X("B"), new Formula.Subscript(X("i"), D(1))), Sp, new Formula.Subscript(X("B"), new Formula.Subscript(X("i"), D(2))), Sp, Seq(Cdot, Cdot, Cdot), Sp, new Formula.Subscript(X("B"), new Formula.Subscript(X("i"), X("m"))), Sp, Comma, Sp, Sp, Sp, new Formula.Subscript(X("B"), Emptyset), Sp, Colon, Sp, Eq, Sp, D(1))), Text(". The factors always stand in ascending index order.” List.prod of the empty list is one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("starcondition"), DeclarationHandle.Create(Prefix + "StarCondition"), H("The star condition"),
                StatementSource.FromAuthor(Disp(Formula4())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Definition D3.3, page 10: “An anticommuting unit family satisfies the star condition if "), Math(Seq(new Formula.Subscript(Seq(Langle, Sp, new Formula.Subscript(X("B"), X("S")), Sp, Rangle), D(0)), Sp, Eq, Sp, D(0))), Text(" for all "), Math(Seq(X("S"), Sp, Neq, Sp, Emptyset)), Text(".” This predicate is not a hypothesis of the formula below."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("c"), DeclarationHandle.Create(Prefix + "c"), H("Half-angle cosine"),
                StatementSource.FromAuthor(Disp(Formula5())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Definition D2.4, page 9: “We write throughout cᵢ := cos(θᵢ/2), sᵢ := sin(θᵢ/2), wᵢ := sᵢ² = sin²(θᵢ/2) ∈ [0,1]”. Each coefficient uses the indexed real angle."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("s"), DeclarationHandle.Create(Prefix + "s"), H("Half-angle sine"),
                StatementSource.FromAuthor(Disp(Formula6())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Definition D2.4, page 9: “We write throughout cᵢ := cos(θᵢ/2), sᵢ := sin(θᵢ/2), wᵢ := sᵢ² = sin²(θᵢ/2) ∈ [0,1]”. Each coefficient uses the indexed real angle."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("w"), DeclarationHandle.Create(Prefix + "w"), H("Sine-square weights"),
                StatementSource.FromAuthor(Disp(Formula7())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Definition D2.4, page 9: “wᵢ := sᵢ² = sin²(θᵢ/2) ∈ [0,1]”. The definition is the square of the sine coefficient."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a"), DeclarationHandle.Create(Prefix + "a"), H("Subset expansion coefficient"),
                StatementSource.FromAuthor(Disp(Formula8())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Definition D2.4, page 9: “and for a subset "), Math(X("S")), Text(" "), Math(Seq(new Formula.Subscript(X("a"), X("S")), Sp, Colon, Sp, Eq, Sp, new Formula.Subscript(Prod, Seq(X("i"), Sp, InMacro, Sp, X("S"))), Sp, new Formula.Subscript(X("s"), X("i")), Sp, new Formula.Subscript(Prod, Seq(X("i"), Sp, Seq(Neg, InMacro), Sp, X("S"))), Sp, new Formula.Subscript(X("c"), X("i")))), Text(".” Complements are taken in Fin k."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rotor"), DeclarationHandle.Create(Prefix + "rotor"), H("Trigonometric rotor"),
                StatementSource.FromAuthor(Disp(Formula9())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Definition D2.3, page 9: “Let B ∈ C be a bivector with B² = −1 and θ ∈ ℝ. Then U(θ) = exp((θ/2)B) = cos(θ/2) + B sin(θ/2) is called the rotor generated by B with parameter θ.” Scalars enter by algebraMap and scalar multiplication."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("chain"), DeclarationHandle.Create(Prefix + "chain"), H("Ordered rotor chain"),
                StatementSource.FromAuthor(Disp(Formula10())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Section 1.1, page 3: “We consider the ordered chain Pₖ = U₁U₂⋯Uₖ”. List.finRange preserves the source order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("returnproduct"), DeclarationHandle.Create(Prefix + "returnProduct"), H("Permuted reversed factors"),
                StatementSource.FromAuthor(Disp(Formula11())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Definition D5.2, page 18: “Let τ be a permutation of {1, …, k}. We set Qₖ⁽τ⁾ = Ũτ₍₁₎ Ũτ₍₂₎ ⋯ Ũτ₍ₖ₎, Θₖ(τ) = PₖQₖ⁽τ⁾”. CliffordAlgebra.reverse is the native reversion."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("loop"), DeclarationHandle.Create(Prefix + "loop"), H("Permuted rotor loop"),
                StatementSource.FromAuthor(Disp(Formula12())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Definition D5.2, page 18: “Θₖ(τ) = PₖQₖ⁽τ⁾”. Both factors are ordered native Clifford products."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("inversioncount"), DeclarationHandle.Create(Prefix + "inversionCount"), H("Restricted inversions"),
                StatementSource.FromAuthor(Disp(Formula13())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Definition D5.2, page 18: “For S ⊆ {1, …, k} let ι(τ, S) := #{(i, j) ∈ S × S : i < j, τ⁻¹(i) > τ⁻¹(j)} be the inversion count of τ on S.” Each ordered pair is counted once."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eta"), DeclarationHandle.Create(Prefix + "eta"), H("Period-four sign"),
                StatementSource.FromAuthor(Disp(Formula14())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Definition D5.1, page 16: “We set for m ∈ ℕ₀ η(m) := (−1)ᵐ · (−1)ᵐ⁽ᵐ⁺¹⁾⁄² = (−1)ᵐ⁽ᵐ⁺³⁾⁄².” Nat.div is natural-number division."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"), H("The formula without the star condition"),
                StatementSource.FromAuthor(Disp(Formula15())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Remark 5.7 in the TeX, rendered Remark 5.5, page 19: “The hypotheses of Theorem 5.5 can be sharpened at two points. First, for τ = id no star condition is needed: that is Theorem 5.2, whose pairing argument cancels the odd off-diagonal terms in pairs. Second, this pairing argument fails termwise for τ ≠ id. Nevertheless, numerical evidence suggests that the formula also holds without the star condition in that case: tested on the triangle family from Remark 4.4, which violates the star condition, under all six permutations of {1, 2, 3} with random parameter sets; the largest deviation encountered was in the range of double machine precision. A general proof would have to capture the cancellation of the odd off-diagonal terms in coarser groups than pairs; we have not determined such a grouping.” The form is real, finite-dimensional and nondegenerate; k is positive. Fin k relabels the source indices increasingly. Every angle and permutation is quantified; the star condition is absent."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nativebridge-scalar-cyclic"), DeclarationHandle.Create(Prefix + "scalar_cyclic"), H("Cyclicity of the native scalar coefficient"),
                StatementSource.FromAuthor(Disp(Formula16())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Lemma 2.1 in the TeX, rendered Lemma 2.3, page 8: “For all x, y ∈ C, ⟨xy⟩₀ = ⟨yx⟩₀.” The native contraction proof also applies to degenerate forms and spaces of arbitrary dimension."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nativegrade-reverse-rotor"), DeclarationHandle.Create(Prefix + "reverse_rotor"), H("Reversion of a bivector rotor"),
                StatementSource.FromAuthor(Disp(Formula17())), AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Definition D2.3, page 9: “We have Ũ(θ) = cos(θ/2) − B sin(θ/2) = U(−θ)”. Homogeneous degree two suffices; the square condition is unnecessary for this identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coefficient-square"), DeclarationHandle.Create(Prefix + "coefficient_square"), H("Squares of subset coefficients"),
                StatementSource.FromAuthor(Disp(Formula18())), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Squaring the subset coefficient replaces sine factors by w and cosine factors by 1 − w. This remains valid when either trigonometric factor vanishes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tracesupport-tracial-subset-vanishing"), DeclarationHandle.Create(Prefix + "tracial_subset_vanishing"), H("Scalar support of an anticommuting family"),
                StatementSource.FromAuthor(Disp(Formula19())), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A nonempty ordered product has zero value under a real linear tracial functional, except possibly when its support is full and the family size is odd. An anticommuting conjugation changes the sign in every other case."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tracesupport-tracial-off-diagonal-zero"), DeclarationHandle.Create(Prefix + "tracial_off_diagonal_zero"), H("Off-diagonal scalar products vanish"),
                StatementSource.FromAuthor(Disp(Formula20())), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Two different subset products have zero tracial pairing unless the family size is odd and their supports are complementary. The statement makes no independence assumption."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("tracesupport-anticommuting-list-square"), DeclarationHandle.Create(Prefix + "anticommuting_list_square"), H("Square of an ordered anticommuting product"),
                StatementSource.FromAuthor(Disp(Formula21())), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A product of distinct anticommuting elements squaring to −1 has square (−1) to the triangular exponent. The order is arbitrary and the carrier is any real algebra."))), DescribeRole.Theorem))));

    private static Formula Formula0() => All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", Real, X("V")), All(X("q"), Call("QuadraticForm", Real, X("V")), All(X("x"), Call("CliffordAlgebra", X("q")), Equal(Call("scalarProjection", X("q"), X("x")), Call("ExteriorAlgebra.algebraMapInv", Call("CliffordAlgebra.equivExterior", X("q"), X("x")))))))));

    private static Formula Formula1() => All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", Real, X("V")), All(X("q"), Call("QuadraticForm", Real, X("V")), All(X("x"), Call("CliffordAlgebra", X("q")), Equal(Call("IsBivector", X("q"), X("x")), MemberOf(Call("CliffordAlgebra.equivExterior", X("q"), X("x")), Call("ExteriorAlgebra.exteriorPower", Real, D(2), X("V")))))))));

    private static Formula Formula2() => All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", Real, X("V")), All(X("q"), Call("QuadraticForm", Real, X("V")), All(X("k"), Nat, All(X("B"), Arrow(Call("Fin", X("k")), Call("CliffordAlgebra", X("q"))), Equal(Call("AnticommutingUnitFamily", X("q"), X("k"), X("B")), AndFormula(All(X("i"), Call("Fin", X("k")), Call("IsBivector", X("q"), App(X("B"), X("i")))), AndFormula(All(X("i"), Call("Fin", X("k")), Equal(Power(App(X("B"), X("i")), D(2)), Negative(D(1)))), All(X("i"), Call("Fin", X("k")), All(X("j"), Call("Fin", X("k")), ImpliesFormula(NotEqual(X("i"), X("j")), Equal(Multiply(App(X("B"), X("i")), App(X("B"), X("j"))), Negative(Multiply(App(X("B"), X("j")), App(X("B"), X("i")))))))))))))))));

    private static Formula Formula3() => All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", Real, X("V")), All(X("q"), Call("QuadraticForm", Real, X("V")), All(X("k"), Nat, All(X("B"), Arrow(Call("Fin", X("k")), Call("CliffordAlgebra", X("q"))), All(X("S"), Call("Finset", Call("Fin", X("k"))), Equal(Call("subsetProduct", X("B"), X("S")), Member(App(Member(App(Member(X("S"), "sort"), Fn(X("u"), Fn(X("v"), LessEqual(X("u"), X("v"))))), "map"), X("B")), "prod")))))))));

    private static Formula Formula4() => All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", Real, X("V")), All(X("q"), Call("QuadraticForm", Real, X("V")), All(X("k"), Nat, All(X("B"), Arrow(Call("Fin", X("k")), Call("CliffordAlgebra", X("q"))), Equal(Call("StarCondition", X("B")), All(X("S"), Call("Finset", Call("Fin", X("k"))), ImpliesFormula(Member(X("S"), "Nonempty"), Equal(Call("scalarProjection", X("q"), Call("subsetProduct", X("B"), X("S"))), D(0)))))))))));

    private static Formula Formula5() => All(X("k"), Nat, All(X("theta"), Arrow(Call("Fin", X("k")), Real), All(X("i"), Call("Fin", X("k")), Equal(Call("c", X("theta"), X("i")), Call("Real.cos", new Formula.Fraction(App(X("theta"), X("i")), D(2)))))));

    private static Formula Formula6() => All(X("k"), Nat, All(X("theta"), Arrow(Call("Fin", X("k")), Real), All(X("i"), Call("Fin", X("k")), Equal(Call("s", X("theta"), X("i")), Call("Real.sin", new Formula.Fraction(App(X("theta"), X("i")), D(2)))))));

    private static Formula Formula7() => All(X("k"), Nat, All(X("theta"), Arrow(Call("Fin", X("k")), Real), All(X("i"), Call("Fin", X("k")), Equal(Call("w", X("theta"), X("i")), Power(Call("s", X("theta"), X("i")), D(2))))));

    private static Formula Formula8() => All(X("k"), Nat, All(X("theta"), Arrow(Call("Fin", X("k")), Real), All(X("S"), Call("Finset", Call("Fin", X("k"))), Equal(Call("a", X("theta"), X("S")), Multiply(Product(X("i"), X("S"), Call("s", X("theta"), X("i"))), Product(X("i"), SetDifference(Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))), X("S")), Call("c", X("theta"), X("i"))))))));

    private static Formula Formula9() => All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", Real, X("V")), All(X("q"), Call("QuadraticForm", Real, X("V")), All(X("k"), Nat, All(X("B"), Arrow(Call("Fin", X("k")), Call("CliffordAlgebra", X("q"))), All(X("theta"), Arrow(Call("Fin", X("k")), Real), All(X("i"), Call("Fin", X("k")), Equal(Call("rotor", X("B"), X("theta"), X("i")), Add(Call("algebraMap", Real, Call("CliffordAlgebra", X("q")), Call("c", X("theta"), X("i"))), Smul(Call("s", X("theta"), X("i")), App(X("B"), X("i")))))))))))));

    private static Formula Formula10() => All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", Real, X("V")), All(X("q"), Call("QuadraticForm", Real, X("V")), All(X("k"), Nat, All(X("B"), Arrow(Call("Fin", X("k")), Call("CliffordAlgebra", X("q"))), All(X("theta"), Arrow(Call("Fin", X("k")), Real), Equal(Call("chain", X("B"), X("theta")), Member(App(Member(Call("List.finRange", X("k")), "map"), Call("rotor", X("B"), X("theta"))), "prod")))))))));

    private static Formula Formula11() => All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", Real, X("V")), All(X("q"), Call("QuadraticForm", Real, X("V")), All(X("k"), Nat, All(X("B"), Arrow(Call("Fin", X("k")), Call("CliffordAlgebra", X("q"))), All(X("theta"), Arrow(Call("Fin", X("k")), Real), All(X("tau"), Call("Equiv.Perm", Call("Fin", X("k"))), Equal(Call("returnProduct", X("B"), X("theta"), X("tau")), Member(App(Member(Call("List.finRange", X("k")), "map"), Fn(X("j"), Call("CliffordAlgebra.reverse", Call("rotor", X("B"), X("theta"), App(X("tau"), X("j")))))), "prod"))))))))));

    private static Formula Formula12() => All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", Real, X("V")), All(X("q"), Call("QuadraticForm", Real, X("V")), All(X("k"), Nat, All(X("B"), Arrow(Call("Fin", X("k")), Call("CliffordAlgebra", X("q"))), All(X("theta"), Arrow(Call("Fin", X("k")), Real), All(X("tau"), Call("Equiv.Perm", Call("Fin", X("k"))), Equal(Call("loop", X("B"), X("theta"), X("tau")), Multiply(Call("chain", X("B"), X("theta")), Call("returnProduct", X("B"), X("theta"), X("tau"))))))))))));

    private static Formula Formula13() => All(X("k"), Nat, All(X("tau"), Call("Equiv.Perm", Call("Fin", X("k"))), All(X("S"), Call("Finset", Call("Fin", X("k"))), Equal(Call("inversionCount", X("tau"), X("S")), Member(App(Member(Call("Finset.product", X("S"), X("S")), "filter"), Fn(X("p"), AndFormula(LessThan(Member(X("p"), "fst"), Member(X("p"), "snd")), LessThan(App(Member(X("tau"), "symm"), Member(X("p"), "snd")), App(Member(X("tau"), "symm"), Member(X("p"), "fst")))))), "card")))));

    private static Formula Formula14() => All(X("m"), Nat, Equal(Call("eta", X("m")), Multiply(Power(Cast(Negative(D(1)), Real), X("m")), Power(Cast(Negative(D(1)), Real), Call("Nat.div", Multiply(X("m"), Add(X("m"), D(1))), D(2))))));

    private static Formula Formula15() => Equal(Call("claim"), All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", Real, X("V")), Instance(Call("FiniteDimensional", Real, X("V")), All(X("q"), Call("QuadraticForm", Real, X("V")), ImpliesFormula(Member(X("q"), "Nondegenerate"), All(X("k"), Nat, ImpliesFormula(LessEqual(D(1), X("k")), All(X("B"), Arrow(Call("Fin", X("k")), Call("CliffordAlgebra", X("q"))), ImpliesFormula(Call("AnticommutingUnitFamily", X("q"), X("k"), X("B")), All(X("theta"), Arrow(Call("Fin", X("k")), Real), All(X("tau"), Call("Equiv.Perm", Call("Fin", X("k"))), Equal(Call("scalarProjection", X("q"), Call("loop", X("B"), X("theta"), X("tau"))), Summation(X("S"), Member(Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))), "powerset"), Multiply(Multiply(Multiply(Call("eta", Member(X("S"), "card")), Power(Cast(Negative(D(1)), Real), Call("inversionCount", X("tau"), X("S")))), Product(X("i"), X("S"), Call("w", X("theta"), X("i")))), Product(X("i"), SetDifference(Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))), X("S")), Subtract(D(1), Call("w", X("theta"), X("i"))))))))))))))))))));

    private static Formula Formula16() => All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", Real, X("V")), All(X("q"), Call("QuadraticForm", Real, X("V")), All(X("x"), Call("CliffordAlgebra", X("q")), All(X("y"), Call("CliffordAlgebra", X("q")), Equal(Call("scalarProjection", X("q"), Multiply(X("x"), X("y"))), Call("scalarProjection", X("q"), Multiply(X("y"), X("x"))))))))));

    private static Formula Formula17() => All(X("V"), Type, Instance(Call("AddCommGroup", X("V")), Instance(Call("Module", Real, X("V")), All(X("q"), Call("QuadraticForm", Real, X("V")), All(X("k"), Nat, All(X("B"), Arrow(Call("Fin", X("k")), Call("CliffordAlgebra", X("q"))), ImpliesFormula(All(X("i"), Call("Fin", X("k")), Call("IsBivector", X("q"), App(X("B"), X("i")))), All(X("theta"), Arrow(Call("Fin", X("k")), Real), All(X("i"), Call("Fin", X("k")), Equal(Call("CliffordAlgebra.reverse", Call("rotor", X("B"), X("theta"), X("i"))), Subtract(Call("algebraMap", Real, Call("CliffordAlgebra", X("q")), Call("c", X("theta"), X("i"))), Smul(Call("s", X("theta"), X("i")), App(X("B"), X("i"))))))))))))));

    private static Formula Formula18() => All(X("k"), Nat, All(X("theta"), Arrow(Call("Fin", X("k")), Real), All(X("S"), Call("Finset", Call("Fin", X("k"))), Equal(Power(Call("a", X("theta"), X("S")), D(2)), Multiply(Product(X("i"), X("S"), Call("w", X("theta"), X("i"))), Product(X("i"), SetDifference(Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))), X("S")), Subtract(D(1), Call("w", X("theta"), X("i")))))))));

    private static Formula Formula19() => All(X("A"), TypeStar, Instance(Call("Ring", X("A")), Instance(Call("Algebra", Real, X("A")), All(X("k"), Nat, All(X("t"), Call("LinearMap", Real, X("A"), Real), ImpliesFormula(All(X("x"), X("A"), All(X("y"), X("A"), Equal(App(X("t"), Multiply(X("x"), X("y"))), App(X("t"), Multiply(X("y"), X("x")))))), All(X("B"), Arrow(Call("Fin", X("k")), X("A")), ImpliesFormula(All(X("i"), Call("Fin", X("k")), Equal(Multiply(App(X("B"), X("i")), App(X("B"), X("i"))), Negative(D(1)))), ImpliesFormula(All(X("i"), Call("Fin", X("k")), All(X("j"), Call("Fin", X("k")), ImpliesFormula(NotEqual(X("i"), X("j")), Equal(Multiply(App(X("B"), X("i")), App(X("B"), X("j"))), Negative(Multiply(App(X("B"), X("j")), App(X("B"), X("i")))))))), All(X("S"), Call("Finset", Call("Fin", X("k"))), ImpliesFormula(Member(X("S"), "Nonempty"), ImpliesFormula(NotFormula(AndFormula(Equal(X("S"), Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k"))))), Call("Odd", X("k")))), Equal(App(X("t"), Member(App(Member(App(Member(X("S"), "sort"), Fn(X("u"), Fn(X("v"), LessEqual(X("u"), X("v"))))), "map"), X("B")), "prod")), D(0))))))))))))));

    private static Formula Formula20() => All(X("A"), TypeStar, Instance(Call("Ring", X("A")), Instance(Call("Algebra", Real, X("A")), All(X("k"), Nat, All(X("t"), Call("LinearMap", Real, X("A"), Real), ImpliesFormula(All(X("x"), X("A"), All(X("y"), X("A"), Equal(App(X("t"), Multiply(X("x"), X("y"))), App(X("t"), Multiply(X("y"), X("x")))))), All(X("B"), Arrow(Call("Fin", X("k")), X("A")), ImpliesFormula(All(X("i"), Call("Fin", X("k")), Equal(Multiply(App(X("B"), X("i")), App(X("B"), X("i"))), Negative(D(1)))), ImpliesFormula(All(X("i"), Call("Fin", X("k")), All(X("j"), Call("Fin", X("k")), ImpliesFormula(NotEqual(X("i"), X("j")), Equal(Multiply(App(X("B"), X("i")), App(X("B"), X("j"))), Negative(Multiply(App(X("B"), X("j")), App(X("B"), X("i")))))))), All(X("S"), Call("Finset", Call("Fin", X("k"))), All(X("T"), Call("Finset", Call("Fin", X("k"))), ImpliesFormula(NotEqual(X("S"), X("T")), ImpliesFormula(NotFormula(AndFormula(Call("Odd", X("k")), Equal(X("T"), SetDifference(Cast(Call("Finset.univ"), Call("Finset", Call("Fin", X("k")))), X("S"))))), Equal(App(X("t"), Multiply(Member(App(Member(App(Member(X("S"), "sort"), Fn(X("u"), Fn(X("v"), LessEqual(X("u"), X("v"))))), "map"), X("B")), "prod"), Member(App(Member(App(Member(X("T"), "sort"), Fn(X("u"), Fn(X("v"), LessEqual(X("u"), X("v"))))), "map"), X("B")), "prod"))), D(0)))))))))))))));

    private static Formula Formula21() => All(X("A"), TypeStar, Instance(Call("Ring", X("A")), Instance(Call("Algebra", Real, X("A")), All(X("I"), TypeStar, All(X("B"), Arrow(X("I"), X("A")), ImpliesFormula(All(X("i"), X("I"), Equal(Multiply(App(X("B"), X("i")), App(X("B"), X("i"))), Negative(D(1)))), ImpliesFormula(All(X("i"), X("I"), All(X("j"), X("I"), ImpliesFormula(NotEqual(X("i"), X("j")), Equal(Multiply(App(X("B"), X("i")), App(X("B"), X("j"))), Negative(Multiply(App(X("B"), X("j")), App(X("B"), X("i")))))))), All(X("l"), Call("List", X("I")), ImpliesFormula(Member(X("l"), "Nodup"), Equal(Multiply(Member(App(Member(X("l"), "map"), X("B")), "prod"), Member(App(Member(X("l"), "map"), X("B")), "prod")), Smul(Power(Cast(Negative(D(1)), Real), Call("Nat.choose", Add(Member(X("l"), "length"), D(1)), D(2))), Cast(D(1), X("A")))))))))))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Type => X("Type");
    private static Formula TypeStar => Seq(Type, Star);
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula Real => Seq(Mathbb, Grp(X("R")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Name(string name) => Seq(name.Split('.').Select((part, index) =>
        index == 0 ? Seq(Operatorname, Grp(X(part))) : Seq(Dot, Operatorname, Grp(X(part)))).ToArray());
    private static Formula Call(string name, params Formula[] args) => App(Name(name), args);
    private static Formula App(Formula function, params Formula[] args) => args.Length == 0 ? function : new Formula.Apply(function, [.. args]);
    private static Formula Member(Formula value, string name) => Seq(Parenthesized(value), Dot, Name(name));
    private static Formula All(Formula name, Formula type, Formula body) => Seq(Forall, Sp,
        Parenthesized(Seq(name, Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Arrow(Formula source, Formula target) => Parenthesized(Seq(source, Sp, To, Sp, target));
    private static Formula Fn(Formula name, Formula body) => Parenthesized(Seq(Name("fun"), Sp, name, Sp, Mapsto, Sp, body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, Parenthesized(right));
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, Parenthesized(right));
    private static Formula LessEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, Parenthesized(right));
    private static Formula LessThan(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, Parenthesized(right));
    private static Formula MemberOf(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Negative(Formula value) => Seq(Minus, Parenthesized(value));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(Parenthesized(value), exponent);
    private static Formula Smul(Formula scalar, Formula value) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(value));
    private static Formula ImpliesFormula(Formula premise, Formula conclusion) => new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies, Parenthesized(conclusion));
    private static Formula AndFormula(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula NotFormula(Formula body) => new Formula.Not(Parenthesized(body));
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula SetDifference(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Setminus, Sp, Parenthesized(right));
    private static Formula Product(Formula name, Formula set, Formula body) => Seq(new Formula.Subscript(Prod, Seq(name, Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
    private static Formula Summation(Formula name, Formula set, Formula body) => Seq(new Formula.Subscript(Sum, Seq(name, Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
}
