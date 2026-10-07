using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.HiguchiSudbery;

internal sealed class HiguchiSudberyEntropyMaximumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit Higuchi–Sudbery state attains the sharp upper bound for the average two-qubit marginal entropy.",
        H("HiguchiSudberyEntropyMaximum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("m4"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum.M4"),
                H("The Higuchi–Sudbery amplitudes"),
                StatementSource.FromAuthor(Disp(All("i", FinSixteen, Eqn(At(Mfour, F.Id("i")), Seq(new Formula.Fraction(D(1), Qualified("Complex", "ofReal", Qualified("Real", "sqrt", D(6)))), Cdot, Sp, Parenthesized(Call("ite", Or(Eqn(F.Id("i"), D(3)), Eqn(F.Id("i"), D(1, 2))), D(1), Call("ite", Or(Eqn(F.Id("i"), D(5)), Eqn(F.Id("i"), D(1, 0))), Qualified("QuditSwappingProductBoundRefutation", "omega", D(3)), Call("ite", Or(Eqn(F.Id("i"), D(6)), Eqn(F.Id("i"), D(9))), new Formula.Power(Qualified("QuditSwappingProductBoundRefutation", "omega", D(3)), D(2)), D(0)))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/higuchisudbery2000entangledcouples")),
                Blocks(Paragraph(Text("Section 3, p. 5: |M₄⟩ = 1/√6 [|0011⟩ + |1100⟩ + ω(|1010⟩ + |0101⟩) + ω²(|1001⟩ + |0110⟩)]. The basis index is 8a+4b+2c+d. The piecewise values are complex and the real square root is coerced to Complex."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum.claim"),
                H("The Higuchi–Sudbery maximum claim"),
                StatementSource.FromAuthor(Disp(Eqn(Call("claim"), ClaimFormula()))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/higuchisudbery2000entangledcouples")),
                Blocks(Paragraph(Text("Section 3, p. 5: “Given that a four-qubit state cannot have maximal entropy of entanglement for every two-qubit subset, we now ask what is the greatest possible average for such entropies, i.e. we seek to maximise”. The displayed average is one third of the AB, AC and AD entropies. The encoding uses all normalized vectors Fin 16 → Complex, with index 8a+4b+2c+d. The second conjunct is attainment at the explicit M4 and does not assert uniqueness."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/HiguchiSudbery/HiguchiSudberyEntropyMaximum.result"),
                H("Sharp global bound and attainment"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumStates/higuchisudbery2000entangledcouples")),
                Blocks(Paragraph(Text("The proof combines the cubic negMulLog majorant, the purity lower bound, and the exact degree-six minor certificate. The marginal spectra of M4 attain equality."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("higuchi-sudbery-2000-four-qubit-average-entropy-maximum"),
                    ResolutionKind.Proved)))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name))), [.. args]);
    private static Formula At(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, Parenthesized(body));
    private static Formula Eqn(Formula lhs, Formula rhs) => new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula Leq(Formula lhs, Formula rhs) => new Formula.Relation(lhs, FormulaRelationOperator.LessThanOrEqual, rhs);
    private static Formula And(Formula lhs, Formula rhs) => new Formula.Logic(Parenthesized(lhs), FormulaLogicOperator.And, Parenthesized(rhs));
    private static Formula Or(Formula lhs, Formula rhs) => new Formula.Logic(Parenthesized(lhs), FormulaLogicOperator.Or, Parenthesized(rhs));
    private static Formula Fn(Formula lhs, Formula rhs) => new Formula.TypeArrow(lhs, rhs);
    private static Formula Z => Call("Complex");
    private static Formula FinSixteen => Call("Fin", D(1, 6));
    private static Formula Amp => Fn(FinSixteen, Z);
    private static Formula Mfour => Seq(Operatorname, Grp(F.Id("M"), D(4)));
    private static Formula SumOf(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(name), Sp, InMacro, Sp, type), Sp, body);
    private static Formula Mass(Formula vector) =>
        SumOf("i", FinSixteen, Qualified("Complex", "normSq", At(vector, F.Id("i"))));
    private static Formula BoundValue => Seq(D(1), Plus,
        new Formula.Fraction(D(1), D(2)), Cdot, Sp, Qualified("Real", "logb", D(2), D(3)));
    private static Formula ClaimFormula()
    {
        Formula z = F.Id("z");
        Formula h = F.Id("h");
        Formula universal = All("z", Amp, All("h", Eqn(Mass(z), D(1)),
            Leq(Call("averageEntropy", z, h), BoundValue)));
        Formula attained = Seq(Exists, Sp,
            Parenthesized(Seq(h, Sp, Colon, Sp, Eqn(Mass(Mfour), D(1)))), Comma, Sp,
            Eqn(Call("averageEntropy", Mfour, h), BoundValue));
        return And(universal, attained);
    }

}
