using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedOriginalOrbitGyrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original primitive-path orbits and forward gyration",
        H("Original primitive-path orbits and forward gyration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("countedoriginalorbitgyration-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedOriginalOrbitGyration.numberedWordEquiv"),
                H("Recover all legal original numbered words"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Splitting each original product edge recovers both vertex words and the actual two half-edge labels. Legality supplies the outside seam and dependent endpoint transports. Rejoining proves the inverse equation, including empty fibers and zero vertex counts. Restriction and signed-time periodic extension give an equivalence with actual periodic paths; finite primitivity agrees with the original minimal shift period."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("countedoriginalorbitgyration-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedOriginalOrbitGyration.orbitBasisEquiv"),
                H("The quotient has a unique least numbered representative"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The orbit relation is reachability by nonnegative iterates of the actual forward shift on primitive paths. Periodic coordinate reduction identifies it with cyclic rotation of their finite restrictions. The original edge key compares source, target, then parallel-edge number; its induced lexicographic word key selects a unique least rotation of each primitive word. This yields a bijection from the actual path-orbit quotient to the least-word basis. Finiteness is obtained from the finite legal-word carrier, without graph inhabitedness assumptions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("countedoriginalorbitgyration-3"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedOriginalOrbitGyration.relativeForwardGyration_eq_order_types"),
                H("From actual forward offsets to the order-type lift"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The elementary homeomorphism induces the original primitive-path and orbit equivalences. For an image path x, canonicalForwardOffset is defined as the negative of the least-rotation index k in Fin d. The proved forward-offset equation carries the canonical target representative to x by that many forward shifts. The proved residue formula identifies its image in ZMod d with the integer minus k.")),
                    Paragraph(Text("RelativeForwardGyration sums these offsets over the actual source quotient, through its proved basis equivalence. Reindexing by legal numbered words gives the integer word-weight sum modulo d. The order-type decomposition then yields orderTypeGyrationLift: the finite integer sum of rank-word weights times products of entrywise binomial coefficients. The theorem asserts equality in ZMod d for every n,m and every nonzero d; no desired orbit-sum identity is assumed.")),
                    Paragraph(Text("This uses the classical finite-orbit transversal and necklace/least-rotation method. It supplies one dependency for the original SGCC objective. Full SGCC, image exhaustion, the localized triangle and the full beam/word comparison are not established here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("countedoriginalorbitgyration-periodic-strata"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedOriginalOrbitGyration.periodic_card_eq_sum_minimalPeriod"),
                H("Partition a fixed-period set by its minimal periods"),
                StatementSource.FromAuthor(PeriodicStrataFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For an arbitrary self-map f and a positive natural number n, a point is fixed by the nth iterate exactly when its minimal period divides n. Sending a periodic point to its minimal period and to itself gives a bijection with the disjoint union of the minimal-period strata indexed by the divisors of n.")),
                    Paragraph(Text("Assume only that the set fixed by the nth iterate is finite. Every divisor stratum injects into that set, so each stratum is finite. Cardinality of the disjoint union is therefore the sum of the stratum cardinalities. The ambient type may be infinite or empty, the strata may be empty, and f need not be invertible. Positivity of n ensures that its divisor set contains every occurring minimal period."))),
                DescribeRole.Theorem))));

    private static Formula PeriodicStrataFormula()
    {
        Formula a = F.Id("A"), f = F.Id("f"), n = F.Id("n");
        Formula d = F.Id("d"), x = F.Id("x");
        Formula periodic = Seq(OpenBrace, x, Colon, Sp, a, Sp, Mid, Sp,
            Call("IsPeriodicPt", f, n, x), CloseBrace);
        Formula stratum = Seq(OpenBrace, x, Colon, Sp, a, Sp, Mid, Sp,
            Call("minimalPeriod", f, x), Sp, Eq, Sp, d, CloseBrace);
        return Disp(Seq(
            Forall, Sp, a, Colon, Sp, Operatorname, Grp(F.Id("Type")), Star, Comma, Sp,
            f, Colon, Sp, a, Sp, To, Sp, a, Comma, Sp,
            n, Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            D(0), Sp, Lt, Sp, n, Sp, Rightarrow, Sp,
            Call("Finite", periodic), Sp, Rightarrow, Esc,
            Cardinality(periodic), Sp, Eq, Sp,
            Sum, Underscore, Grp(d, Sp, InMacro, Sp, Call("divisors", n)), Sp,
            Cardinality(stratum)));
    }

    private static Formula Cardinality(Formula carrier) =>
        Seq(Operatorname, Grp(F.Id("Nat"), Dot, F.Id("card")), Open, carrier, Close);

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new System.Collections.Generic.List<Formula>
            { Operatorname, Grp(F.Id(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq(items.ToArray());
    }
}
