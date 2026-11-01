using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class FewerEffectsOrthogonalityRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurements/FewerEffectsOrthogonalityRefutation";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Estimation/liudebrota2021orthogonality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four effects on a ten-dimensional complex space disprove the proposed orthogonality minimum.",
        H("Orthogonality with fewer effects than dimensions"),
        Blocks(
            Node("gram", "The square-root Gram matrix", GramFormula(),
                "For a family f of complex matrices, the (i,j) entry is "
                    + "GeneralizedFidelity.fidelity 1 (f i) (f j). At reference matrix 1, this is "
                    + "the trace of the product of CFC.sqrt (f i) and CFC.sqrt (f j). For positive "
                    + "semidefinite effects these are the positive square roots, giving the source's "
                    + "entry [S] at (i,j) and its Hilbert–Schmidt Gram matrix. "
                    + "The formula accepts arbitrary complex matrices without a positivity hypothesis. "
                    + "It expresses the definition in Section IV, apssamp.tex, lines 403–406.",
                AssessedProvenance.FromLiterature(Source)),
            Node("orthogonality", "Squared distance from the identity", OrthogonalityFormula(),
                "Orthogonality applies CHaarConcatenationNonmonotone.hsNormSq to the Gram matrix "
                    + "minus the n by n identity. This is the sum of the squared complex moduli "
                    + "of its entries, taking values in the real numbers: the source's squared "
                    + "Frobenius distance of S from the identity in Section IV, "
                    + "apssamp.tex, lines 410–420; the definition itself does not assume that f is a POVM.",
                AssessedProvenance.FromLiterature(Source)),
            Node("IsPOVMWith", "Exactly n nonzero effects", IsPOVMWithFormula(),
                "Every matrix f i must be positive semidefinite and nonzero, and the sum of "
                    + "the effects must be the d by d identity. Distinct indices are not required "
                    + "to have distinct matrices. The POVM conditions occur in apssamp.tex, line 155; "
                    + "the nonvanishing condition is part of the conjecture at lines 795–797.",
                AssessedProvenance.FromLiterature(Source)),
            Node("construction", "Consecutive coordinate blocks", ConstructionFormula(),
                "The diagonal entry at coordinate k is one precisely when k lies in the block "
                    + "assigned to i. All coordinate values are natural numbers, obtained explicitly "
                    + "by Fin.val, and Nat.div is natural-number division. Subtraction in n minus one "
                    + "is natural-number subtraction. For 0 < n < d, write d = an + b with a = d / n "
                    + "and 0 ≤ b < n. The first n minus one blocks have a coordinates each; the last "
                    + "has a + b. These disjoint blocks give the diagonal projectors described in "
                    + "Appendix C, apssamp.tex, lines 761–792. The formula defines a family for every "
                    + "natural n and d, including the empty family when n is zero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The proposed minimum for fewer effects", ClaimFormula(),
                "For every pair of natural dimensions with 0 < n < d, the proposed block family "
                    + "is asserted to have orthogonality no greater than any POVM with exactly n "
                    + "nonzero effects. This is the universal statement corresponding to Conjecture 2 "
                    + "in Appendix C, apssamp.tex, lines 795–797, with the consecutive blocks above "
                    + "fixing the coordinate representation of its construction.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Four effects in dimension ten refute the minimum"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "At n = 4 and d = 10, the proposed construction consists of coordinate "
                            + "projectors with ranks 2, 2, 2, 4. Each diagonal entry is zero or one. "
                            + "NMLWMeasuredFidelitySeparation.sqrt_diagonal computes the positive "
                            + "square root by taking the real square root of each nonnegative diagonal "
                            + "entry. Since the square roots of zero and one are zero and one, "
                            + "each matrix is its own positive square root.")),
                    Paragraph(Text(
                        "Define another family F of diagonal projectors on the consecutive coordinate "
                            + "blocks [0,2), [2,4), [4,7), [7,10). Its ranks are 2, 2, 3, 3. "
                            + "The same diagonal square-root formula makes each of these "
                            + "matrices its own positive square root.")),
                    Paragraph(Text(
                        "For the proposed construction, multiply the diagonal square roots and "
                            + "sum their diagonal entries to take the trace. Disjoint supports make "
                            + "the off-diagonal Gram entries zero; the diagonal entries are the block "
                            + "ranks. Thus its Gram matrix is diag(2,2,2,4). Applying the same "
                            + "entrywise calculation to F gives diag(2,2,3,3).")),
                    Paragraph(Text(
                        "The family F has positive semidefinite effects because its diagonal "
                            + "entries are nonnegative. None is zero: a zero effect would have zero "
                            + "square root and zero diagonal Gram entry, contradicting its positive "
                            + "rank. Summing the four matrices entry by entry gives the identity, "
                            + "since the blocks partition all ten coordinates. Hence F satisfies "
                            + "IsPOVMWith 4 10.")),
                    Paragraph(Text(
                        "Subtracting the four by four identity from the first Gram matrix and "
                            + "summing the squared complex moduli gives 1 + 1 + 1 + 9 = 12. "
                            + "For F the corresponding sum is 1 + 1 + 4 + 4 = 10. "
                            + "If claim held, its instance at n = 4, d = 10 and F would imply "
                            + "12 ≤ 10, a contradiction. The proposed minimum is therefore false. "
                            + "This comparison does not assert the minimum among all such POVMs."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("liu-debrota-2021-fewer-effects-orthogonality"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(declaration == "IsPOVMWith" ? "is-povm-with" : declaration),
            DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula GramFormula() => FamilyBinders(Equal(
        Typed(LocalCall("gram", X("f")), Mat(X("n"))),
        LambdaOf("i", FinOf(X("n")), LambdaOf("j", FinOf(X("n")),
            At(Qualified("D5", "S3", "Quantum", "GeneralizedFidelity", "fidelity"),
                Typed(D(1), Mat(X("d"))), At(X("f"), X("i")), At(X("f"), X("j")))))));

    private static Formula OrthogonalityFormula() => FamilyBinders(Equal(
        Typed(LocalCall("orthogonality", X("f")), Reals()),
        At(Qualified("D5", "S3", "Quantum", "RandomCircuits", "CHaarConcatenationNonmonotone", "hsNormSq"),
            Subtract(LocalCall("gram", X("f")), Typed(D(1), Mat(X("n")))))));

    private static Formula IsPOVMWithFormula() => FamilyBinders(Equivalence(
        LocalCall("IsPOVMWith", X("n"), X("d"), X("f")),
        And(All("i", FinOf(X("n")), And(
                At(Qualified("Matrix", "PosSemidef"), At(X("f"), X("i"))),
                NotEqual(At(X("f"), X("i")), Typed(D(0), Mat(X("d")))))),
            Equal(SumOver("i", FinOf(X("n")), At(X("f"), X("i"))),
                Typed(D(1), Mat(X("d")))))));

    private static Formula ConstructionFormula()
    {
        Formula quotient = At(Qualified("Nat", "div"), X("d"), X("n"));
        Formula upper = If(LT(FinValue("i"), Subtract(X("n"), Typed(D(1), Naturals()))),
            Multiply(Add(FinValue("i"), Typed(D(1), Naturals())), quotient), X("d"));
        Formula inside = And(LE(Multiply(FinValue("i"), quotient), FinValue("k")),
            LT(FinValue("k"), upper));
        Formula diagonal = At(Qualified("Matrix", "diagonal"), LambdaOf("k", FinOf(X("d")),
            If(inside, Typed(D(1), Complexes()), Typed(D(0), Complexes()))));
        return Dimensions(Equal(Typed(LocalCall("construction", X("n"), X("d")), Family()),
            LambdaOf("i", FinOf(X("n")), diagonal)));
    }

    private static Formula ClaimFormula() => Equivalence(Local("claim"), Dimensions(
        ImpliesFormula(LT(Typed(D(0), Naturals()), X("n")),
            ImpliesFormula(LT(X("n"), X("d")), All("f", Family(),
                ImpliesFormula(LocalCall("IsPOVMWith", X("n"), X("d"), X("f")),
                    LE(LocalCall("orthogonality", LocalCall("construction", X("n"), X("d"))),
                        LocalCall("orthogonality", X("f")))))))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Measurements",
        "FewerEffectsOrthogonalityRefutation", name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula FinValue(string name) => Typed(At(Qualified("Fin", "val"), X(name)), Naturals());
    private static Formula Mat(Formula size) => At(Qualified("Matrix"), FinOf(size), FinOf(size), Complexes());
    private static Formula Family() => Arrow(FinOf(X("n")), Mat(X("d")));
    private static Formula Dimensions(Formula body) => All("n", Naturals(), All("d", Naturals(), body));
    private static Formula FamilyBinders(Formula body) => Dimensions(All("f", Family(), body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        At(Qualified("ite"), Parenthesized(condition), yes, no);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
