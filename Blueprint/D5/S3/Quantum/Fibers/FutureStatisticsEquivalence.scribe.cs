using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class FutureStatisticsEquivalenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Future operator statistics are exactly the annihilator of the generated system.",
        H("Future Statistics and the Infinite Operator System"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("future-statistics-iff-annihilates-infinite-system"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Fibers/FutureStatisticsEquivalence."
                        + "future_statistics_iff_annihilates_infinite_system"),
                H("Future statistics characterize the infinite-system annihilator"),
                StatementSource.FromAuthor(EquivalenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The states are positive trace-one matrices on a finite complex matrix "
                            + "carrier. The Schrödinger map is completely positive and "
                            + "trace-preserving, while its Heisenberg dual is completely positive, "
                            + "unital, and satisfies the displayed trace-duality identity.")),
                    Paragraph(Text(
                        "The initial operator system is a real subspace of the full Hermitian "
                            + "carrier containing the identity. The infinite prediction system is "
                            + "the real span of every finite Heisenberg iterate of every initial "
                            + "effect.")),
                    Paragraph(Text(
                        "Equality of the complete initial-system readout after every finite channel "
                            + "iterate is equivalent to zero trace pairing of the state difference "
                            + "with every effect in that generated system."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Trace(Formula value) =>
        Seq(Operatorname, Grp(F.Id("Tr")), Open, value, Close);

    private static Formula Iterate(Formula map, Formula index, Formula value) =>
        Seq(Open, map, Close, Caret, Grp(index), Open, value, Close);

    private static Formula EquivalenceFormula()
    {
        Formula d = F.Id("d");
        Formula k = F.Id("k");
        Formula state = F.Id("X");
        Formula effect = F.Id("A");
        Formula initialEffect = F.Id("E");
        Formula channel = Phi;
        Formula heisenberg = Seq(Phi, Caret, Grp(Star));
        Formula rho = Rho;
        Formula sigma = SigmaLower;
        Formula initial = Seq(F.Id("S"), Underscore, Grp(D(0)));
        Formula infinite = Seq(F.Id("S"), Underscore, Grp(Infty));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula matrix = Call("Matrix", d, d, complex);
        Formula hermitian = Call("Hermitian", matrix);
        Formula channelType = Call("QuantumChannel", d, d);
        Formula mapType = Call("CompletelyPositiveMap", matrix, matrix);
        Formula initialType = Call("OperatorSystem", hermitian);
        Formula densityType = Call("DensityState", d);
        Formula generatedSet = Seq(
            Left, OpenBrace,
            Iterate(heisenberg, k, initialEffect), Sp, Mid, Sp,
            k, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            initialEffect, InMacro, Sp, initial,
            Right, CloseBrace);
        Formula generatedSpan = Seq(
            Operatorname, Grp(F.Id("span")), Underscore, Grp(real),
            Open, generatedSet, Close);
        Formula rhoEvolved = Call("evolvedState", channel, k, rho);
        Formula sigmaEvolved = Call("evolvedState", channel, k, sigma);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, d, Comma, Sp, Call("Finite", d), Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("DecidableEq")), Open, d, Close,
            CloseBracket, Comma, RowBreak, Grp(),
            channel, Colon, Sp, channelType, Comma, Sp,
            heisenberg, Colon, Sp, mapType, Comma, Sp,
            Apply(heisenberg, F.Id("I")), Sp, Eq, Sp, F.Id("I"), Comma, RowBreak, Grp(),
            Forall, Sp, state, Comma, Sp, effect, Colon, Sp, matrix, Comma, Sp,
            Trace(Seq(Apply(channel, state), Sp, effect)), Sp, Eq, Sp,
            Trace(Seq(state, Sp, Apply(heisenberg, effect))), Comma, RowBreak, Grp(),
            initial, Colon, Sp, initialType, Comma, Sp,
            rho, Comma, Sp, sigma, Colon, Sp, densityType, Comma, RowBreak, Grp(),
            infinite, Sp, Colon, Eq, Sp, generatedSpan, Comma, RowBreak, Grp(),
            Open,
            Forall, Sp, k, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            Call("operatorSystemReadout", initial, rhoEvolved), Sp, Eq, Sp,
            Call("operatorSystemReadout", initial, sigmaEvolved),
            Close, RowBreak, Grp(),
            Leftrightarrow, RowBreak, Grp(),
            Forall, Sp, effect, InMacro, Sp, infinite, Comma, Sp,
            Trace(Seq(Open, rho, Minus, sigma, Close, effect)), Sp, Eq, Sp, D(0), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
