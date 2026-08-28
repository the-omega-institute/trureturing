using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementGeometry;

internal sealed class DominancePrecisionIntervalDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/RefinementGeometry/DominancePrecisionInterval."
            + "dominance_precision_interval";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete dominance occupies exactly the half-open band between the two pairwise "
            + "reveal thresholds.",
        H("Dominance Precision Interval"),
        Blocks(Describe.Lean(
            DescribeId.Create("dominance-precision-interval"),
            DeclarationHandle.Create(Declaration),
            H("Complete dominance is an interval of precision levels"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The reveal threshold of a pair is constructed as its least separating "
                        + "precision, with infinity used exactly when no precision separates "
                        + "the pair. Compatibility of the lowering maps makes separation "
                        + "persistent above that threshold.")),
                Paragraph(Text(
                    "Complete dominance at level k is the simultaneous agreement of AA with "
                        + "AB and separation of AB from BB. Consequently its extended-natural "
                        + "levels are precisely the half-open interval from r2 to r1, and such "
                        + "a level exists exactly when r2 is strictly below r1.")),
                Paragraph(Text(
                    "The finite dominance width is constructed as the cardinality of the "
                        + "finite-level dominance band. When both reveal thresholds are finite, "
                        + "the natural interval cardinality theorem identifies it with n1 - n2."))),
            DescribeRole.Theorem))));

    private static Formula Indexed(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula readout = F.Id("q");
        Formula lower = F.Id("rho");
        Formula level = F.Id("k");
        Formula stateAA = Indexed(F.Id("x"), F.Id("AA"));
        Formula stateAB = Indexed(F.Id("x"), F.Id("AB"));
        Formula stateBB = Indexed(F.Id("x"), F.Id("BB"));
        Formula r1 = Indexed(F.Id("r"), D(1));
        Formula r2 = Indexed(F.Id("r"), D(2));
        Formula dominant = F.Id("d");
        Formula band = F.Id("D");
        Formula finiteBand = Indexed(F.Id("D"), F.Id("fin"));
        Formula width = Indexed(F.Id("W"), F.Id("dom"));
        Formula value = F.Id("v");
        Formula n1 = Indexed(F.Id("n"), D(1));
        Formula n2 = Indexed(F.Id("n"), D(2));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula extendedNaturals = Call("WithTop", naturals);
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula next = Seq(level, Plus, D(1));

        Formula Read(Formula index, Formula point) =>
            Apply(Indexed(readout, index), point);

        Formula dominantAt = Apply(dominant, level);
        Formula dominanceDefinition = Seq(
            dominantAt, Sp, Colon, Sp, Eq, Sp,
            Open, Read(level, stateAA), Sp, Eq, Sp, Read(level, stateAB), Sp,
            Land, Sp, Read(level, stateAB), Sp, Neq, Sp, Read(level, stateBB), Close);
        Formula bandDefinition = Seq(
            band, Sp, Colon, Sp, Eq, Sp,
            OpenBrace, value, InMacro, Sp, extendedNaturals, Sp, Mid, Sp,
            Exists, Sp, level, InMacro, Sp, naturals, Comma, Sp,
            value, Sp, Eq, Sp, level, Sp, Land, Sp, dominantAt, CloseBrace);
        Formula finiteBandDefinition = Seq(
            finiteBand, Sp, Colon, Sp, Eq, Sp,
            OpenBrace, level, InMacro, Sp, naturals, Sp, Mid, Sp,
            dominantAt, CloseBrace);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, state, Colon, Sp, type, Comma, Sp,
                output, Colon, Sp, naturals, Sp, To, Sp, type, Comma),
            Seq(
                readout, Colon, Sp, Forall, Sp, level, Colon, Sp, naturals,
                Comma, Sp, state, Sp, To, Sp, Indexed(output, level), Comma),
            Seq(
                lower, Colon, Sp, Forall, Sp, level, Colon, Sp, naturals,
                Comma, Sp, Indexed(output, next), Sp, To, Sp,
                Indexed(output, level), Comma),
            Seq(
                stateAA, Comma, Sp, stateAB, Comma, Sp, stateBB,
                Colon, Sp, state, Comma),
            Seq(
                Open, Forall, Sp, level, Colon, Sp, naturals, Comma, Sp,
                Indexed(readout, level), Sp, Eq, Sp, Indexed(lower, level),
                Sp, Circ, Sp, Indexed(readout, next), Close, Sp, Rightarrow),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                r1, Sp, Colon, Sp, Eq, Sp,
                Call("revealThreshold", output, readout, stateAA, stateAB), Comma),
            Seq(
                r2, Sp, Colon, Sp, Eq, Sp,
                Call("revealThreshold", output, readout, stateAB, stateBB), Comma),
            Seq(dominanceDefinition, Comma),
            Seq(bandDefinition, Comma),
            Seq(finiteBandDefinition, Comma),
            Seq(
                width, Sp, Colon, Sp, Eq, Sp, Call("ncard", finiteBand), Sp,
                Operatorname, Grp(F.Id("in"))),
            Seq(
                Open, Forall, Sp, level, InMacro, Sp, naturals, Comma, Sp,
                dominantAt, Sp, Leftrightarrow, Sp,
                r2, Sp, Leq, Sp, level, Sp, Land, Sp,
                level, Sp, Lt, Sp, r1, Close, Sp, Land),
            Seq(
                band, Sp, Eq, Sp, Call("Ico", r2, r1), Sp, Land),
            Seq(
                Open, Open, Exists, Sp, level, InMacro, Sp, naturals, Comma, Sp,
                dominantAt, Close, Sp, Leftrightarrow, Sp,
                r2, Sp, Lt, Sp, r1, Close, Sp, Land),
            Seq(
                Open, Forall, Sp, n1, Comma, Sp, n2, InMacro, Sp, naturals,
                Comma, Sp, r1, Sp, Eq, Sp, n1, Sp, Land, Sp,
                r2, Sp, Eq, Sp, n2, Sp, Rightarrow, Sp,
                width, Sp, Eq, Sp, n1, Sp, Minus, Sp, n2, Close, Dot),
        ]));
    }
}
