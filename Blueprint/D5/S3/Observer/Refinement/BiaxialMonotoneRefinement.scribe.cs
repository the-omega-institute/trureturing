using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Refinement;

internal sealed class BiaxialMonotoneRefinementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Enlarging either axis of a finite orbit-observation schedule can only shrink indistinguishability.",
        H("Biaxial Monotone Refinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-axis-monotonicity"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Refinement/BiaxialMonotoneRefinement.prime_axis_monotone"),
                H("More observation indices refine indistinguishability"),
                StatementSource.FromAuthor(PrimeAxisFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finite readout-index sets J contained in K and a fixed time horizon m, "
                            + "the K-schedule includes every experiment in the J-schedule. Agreement "
                            + "under all K-indexed observations therefore implies agreement under all "
                            + "J-indexed observations.")),
                    Paragraph(Text(
                        "The resulting relation inclusion runs from Indist K m to Indist J m: adding "
                            + "observation indices can distinguish additional state pairs but cannot "
                            + "make previously distinguishable pairs indistinguishable. No arithmetic "
                            + "primality assumption is needed; only inclusion of the finite index sets "
                            + "is used."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("time-axis-monotonicity"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Refinement/BiaxialMonotoneRefinement.time_axis_monotone"),
                H("Longer observation windows refine indistinguishability"),
                StatementSource.FromAuthor(TimeAxisFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a fixed finite index set J and horizons m at most n, every iterate observed "
                            + "before time m is also observed before time n. The longer schedule therefore "
                            + "contains the shorter schedule.")),
                    Paragraph(Text(
                        "With the indexed readout and transition map unchanged, agreement throughout the "
                            + "n-window implies agreement throughout the m-window. Extending the time "
                            + "horizon can consequently remove indistinguishable pairs but cannot add them."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("biaxial-monotonicity"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Refinement/BiaxialMonotoneRefinement.biaxial_monotone"),
                H("Joint expansion refines indistinguishability"),
                StatementSource.FromAuthor(BiaxialFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If J is contained in K and m is at most n, the schedule indexed by K through "
                            + "time n expands the schedule indexed by J through time m in both coordinates. "
                            + "Any state pair indistinguishable under the larger schedule is therefore "
                            + "indistinguishable under the smaller one.")),
                    Paragraph(Text(
                        "The two refinements are independent: first restrict the observation indices at "
                            + "the longer horizon, then shorten the horizon at the smaller index set. "
                            + "Composing those two relation inclusions gives the joint biaxial inclusion."))),
                DescribeRole.Theorem))));

    private static Formula Indist(
        Formula indices,
        Formula horizon,
        Formula readout,
        Formula transition) =>
        Call("Indist", indices, horizon, readout, transition);

    private static Formula PrimeAxisFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula smaller = F.Id("J");
        Formula larger = F.Id("K");
        Formula horizon = F.Id("m");
        Formula readout = F.Id("readout");
        Formula transition = F.Id("T");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula finiteNaturals = Call("Finset", naturals);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            smaller, Comma, Sp, larger, Colon, Sp, finiteNaturals, Comma, Sp,
            horizon, Colon, Sp, naturals, Comma,
            RowBreak, Grp(),
            readout, Colon, Sp, naturals, Sp, To, Sp, state, Sp, To, Sp, output,
            Comma, Sp, transition, Colon, Sp, state, Sp, To, Sp, state, Comma,
            RowBreak, Grp(),
            smaller, Sp, Subseteq, Sp, larger, Sp, Rightarrow, Sp,
            Indist(larger, horizon, readout, transition), Sp, Subseteq, Sp,
            Indist(smaller, horizon, readout, transition), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula TimeAxisFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula indices = F.Id("J");
        Formula shorter = F.Id("m");
        Formula longer = F.Id("n");
        Formula readout = F.Id("readout");
        Formula transition = F.Id("T");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula finiteNaturals = Call("Finset", naturals);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            indices, Colon, Sp, finiteNaturals, Comma, Sp,
            shorter, Comma, Sp, longer, Colon, Sp, naturals, Comma,
            RowBreak, Grp(),
            readout, Colon, Sp, naturals, Sp, To, Sp, state, Sp, To, Sp, output,
            Comma, Sp, transition, Colon, Sp, state, Sp, To, Sp, state, Comma,
            RowBreak, Grp(),
            shorter, Sp, Leq, Sp, longer, Sp, Rightarrow, Sp,
            Indist(indices, longer, readout, transition), Sp, Subseteq, Sp,
            Indist(indices, shorter, readout, transition), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula BiaxialFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula smaller = F.Id("J");
        Formula larger = F.Id("K");
        Formula shorter = F.Id("m");
        Formula longer = F.Id("n");
        Formula readout = F.Id("readout");
        Formula transition = F.Id("T");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula finiteNaturals = Call("Finset", naturals);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, output, Colon, Sp, type, Comma,
            RowBreak, Grp(),
            smaller, Comma, Sp, larger, Colon, Sp, finiteNaturals, Comma, Sp,
            shorter, Comma, Sp, longer, Colon, Sp, naturals, Comma,
            RowBreak, Grp(),
            readout, Colon, Sp, naturals, Sp, To, Sp, state, Sp, To, Sp, output,
            Comma, Sp, transition, Colon, Sp, state, Sp, To, Sp, state, Comma,
            RowBreak, Grp(),
            smaller, Sp, Subseteq, Sp, larger, Sp, Land, Sp,
            shorter, Sp, Leq, Sp, longer, Sp, Rightarrow, Sp,
            Indist(larger, longer, readout, transition), Sp, Subseteq, Sp,
            Indist(smaller, shorter, readout, transition), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
