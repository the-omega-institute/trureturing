using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class DeterministicReadoutPvmDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deterministic readout fibers form a complete family of diagonal projections.",
        H("Deterministic Readout PVM"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("deterministic-readout-pvm"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Measurements/DeterministicReadoutPvm."
                        + "deterministic_readout_pvm"),
                H("Fiber projections are orthogonal and complete"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite state carrier and deterministic readout, each outcome "
                            + "projection is the diagonal indicator of its readout fiber.")),
                    Paragraph(Text(
                        "Distinct fibers are disjoint, giving the product law; the fibers cover "
                            + "the state carrier, giving the identity sum."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula x = F.Id("X");
        Formula o = F.Id("O");
        Formula readout = F.Id("q");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula outcome = F.Id("o");
        Formula outcomePrime = F.Id("op");
        Formula projection = (Formula)Seq(
            Operatorname, Grp(F.Id("deterministicProjection")));
        Formula p = Seq(projection, Open, readout, Comma, Sp, F.Id("o"), Close);
        Formula pPrime = Seq(projection, Open, readout, Comma, Sp, outcomePrime, Close);
        Formula product = Seq(p, Sp, Circ, Sp, pPrime, Sp, Eq, Sp,
            F.Id("if"), Sp, outcome, Sp, Eq, Sp, outcomePrime, Sp,
            F.Id("then"), Sp, p, Sp, F.Id("else"), Sp, D(0));
        Formula sum = Seq(Subscript(F.Id("sum"), outcome), Sp, p,
            Sp, Eq, Sp, F.Id("I"));
        return Disp(Seq(
            Forall, Sp, Typed(x, type), Comma, Sp,
            Typed(o, type), Comma, Sp,
            Instance("Fintype", x), Comma, Sp,
            Instance("Fintype", o), Comma, Sp,
            Instance("DecidableEq", x), Comma, Sp,
            Instance("DecidableEq", o), Comma, Sp,
            Typed(readout, Arrow(x, o)), Sp, Rightarrow, Sp,
            Forall, Sp, Typed(outcome, o), Comma, Sp,
            Typed(outcomePrime, o), Comma, Sp,
            product, Sp, Land, Sp, sum, Dot));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Instance(string name, Formula value) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, value, Close, CloseBracket);

    private static Formula Subscript(Formula value, Formula subscript) =>
        Seq(value, Underscore, Grp(subscript));
}
