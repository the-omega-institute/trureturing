using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.HiguchiSudbery;

internal sealed class HS4AssemblyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal marginal density states define the average entropy in bits.",
        H("HS4Assembly"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cutindex"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/HiguchiSudbery/HS4Assembly.cutIndex"),
                H("Literal index tables"),
                StatementSource.FromAuthor(Disp(All("c", Fin(3), Eqn(Call("cutIndex", F.Id("c")), At(Seq(Bang, OpenBracket, Seq(Bang, Bang, OpenBracket, D(0), Comma, D(1), Comma, D(2), Comma, D(3), Semi, D(4), Comma, D(5), Comma, D(6), Comma, D(7), Semi, D(8), Comma, D(9), Comma, D(1, 0), Comma, D(1, 1), Semi, D(1, 2), Comma, D(1, 3), Comma, D(1, 4), Comma, D(1, 5), CloseBracket), Comma, Seq(Bang, Bang, OpenBracket, D(0), Comma, D(1), Comma, D(4), Comma, D(5), Semi, D(2), Comma, D(3), Comma, D(6), Comma, D(7), Semi, D(8), Comma, D(9), Comma, D(1, 2), Comma, D(1, 3), Semi, D(1, 0), Comma, D(1, 1), Comma, D(1, 4), Comma, D(1, 5), CloseBracket), Comma, Seq(Bang, Bang, OpenBracket, D(0), Comma, D(2), Comma, D(4), Comma, D(6), Semi, D(1), Comma, D(3), Comma, D(5), Comma, D(7), Semi, D(8), Comma, D(1, 0), Comma, D(1, 2), Comma, D(1, 4), Semi, D(9), Comma, D(1, 1), Comma, D(1, 3), Comma, D(1, 5), CloseBracket), CloseBracket), F.Id("c")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The matrix rows and columns are ordered as 00, 01, 10, 11. The three index tables retain AB, AC and AD, respectively, for the basis index 8a+4b+2c+d."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cutflatten"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/HiguchiSudbery/HS4Assembly.cutFlatten"),
                H("Flattening amplitudes"),
                StatementSource.FromAuthor(Disp(All("z", Amp, All("c", Fin(3), Eqn(Call("cutFlatten", F.Id("z"), F.Id("c")), Seq(Parenthesized(Seq(F.Id("r"), Sp, Colon, Sp, Fin(4))), Sp, Mapsto, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("b"), Sp, Colon, Sp, Fin(4))), Sp, Mapsto, Sp, Parenthesized(At(F.Id("z"), Call("cutIndex", F.Id("c"), F.Id("r"), F.Id("b")))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each matrix entry is the amplitude at the literal cutIndex value; no basis relabeling is hidden in this definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cutmatrix"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/HiguchiSudbery/HS4Assembly.cutMatrix"),
                H("Literal marginal matrix"),
                StatementSource.FromAuthor(Disp(All("z", Amp, All("c", Fin(3), Eqn(Call("cutMatrix", F.Id("z"), F.Id("c")), Call("partialTraceRight", Call("rankOneDensity", Seq(Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Seq(Fin(4), Times, Fin(4)))), Sp, Mapsto, Sp, Parenthesized(Call("cutFlatten", F.Id("z"), F.Id("c"), Seq(F.Id("p"), Dot, D(1)), Seq(F.Id("p"), Dot, D(2)))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The repository’s partialTraceRight and rankOneDensity are reused directly. The carrier is Fin 4 × Fin 4, with the retained pair in the first component."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cutdensity"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/HiguchiSudbery/HS4Assembly.cutDensity"),
                H("Normalized literal marginal"),
                StatementSource.FromAuthor(Disp(All("z", Amp, All("hz", Eqn(Mass(F.Id("z")), D(1)), All("c", Fin(3), All("h", Eqn(Call("dotProduct", Call("star", Seq(Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Seq(Fin(4), Times, Fin(4)))), Sp, Mapsto, Sp, Parenthesized(Call("cutFlatten", F.Id("z"), F.Id("c"), Seq(F.Id("p"), Dot, D(1)), Seq(F.Id("p"), Dot, D(2)))))), Seq(Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Seq(Fin(4), Times, Fin(4)))), Sp, Mapsto, Sp, Parenthesized(Call("cutFlatten", F.Id("z"), F.Id("c"), Seq(F.Id("p"), Dot, D(1)), Seq(F.Id("p"), Dot, D(2)))))), D(1)), Eqn(Call("cutDensity", F.Id("z"), F.Id("hz"), F.Id("c")), Call("marginalRight", Call("pureDensityState", Seq(Parenthesized(Seq(F.Id("p"), Sp, Colon, Sp, Seq(Fin(4), Times, Fin(4)))), Sp, Mapsto, Sp, Parenthesized(Call("cutFlatten", F.Id("z"), F.Id("c"), Seq(F.Id("p"), Dot, D(1)), Seq(F.Id("p"), Dot, D(2))))), F.Id("h")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed h is any proof of the flattened-vector normalization; the amplitude normalization hz supplies it in Lean. Proof irrelevance makes the resulting density state independent of this proof term. Both pureDensityState and marginalRight are reused repository definitions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("averageentropy"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/HiguchiSudbery/HS4Assembly.averageEntropy"),
                H("Average two-qubit entropy"),
                StatementSource.FromAuthor(Disp(All("z", Amp, All("h", Eqn(Mass(F.Id("z")), D(1)), Eqn(Call("averageEntropy", F.Id("z"), F.Id("h")), new Formula.Fraction(SumOf("c", Fin(3), Call("vonNeumannEntropy", Call("cutDensity", F.Id("z"), F.Id("h"), F.Id("c")))), Seq(D(3), Cdot, Sp, Qualified("Real", "log", D(2))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumStates/higuchisudbery2000entangledcouples")),
                Blocks(Paragraph(Text("Section 3, p. 5: “The second equality holds because complementary pairs have equal entropy.” The displayed average (E_AB+E_AC+E_AD)/3 uses the repository’s vonNeumannEntropy divided by log 2, so its units are bits. Index c ranges over Fin 3 in the order AB, AC, AD."))),
                DescribeRole.Definition))));

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
    private static Formula Fn(Formula lhs, Formula rhs) => new Formula.TypeArrow(lhs, rhs);
    private static Formula Z => Call("Complex");
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula FinSixteen => Call("Fin", D(1, 6));
    private static Formula Amp => Fn(FinSixteen, Z);
    private static Formula SumOf(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id(name), Sp, InMacro, Sp, type), Sp, body);
    private static Formula Mass(Formula vector) =>
        SumOf("i", FinSixteen, Qualified("Complex", "normSq", At(vector, F.Id("i"))));

}
