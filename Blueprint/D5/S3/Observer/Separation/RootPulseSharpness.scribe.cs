using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class RootPulseSharpnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The root-pulse chain attains the finite observation refinement bound exactly.",
        H("Root Pulse Sharpness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("root-pulse-sharpness"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/RootPulseSharpness.root_pulse_sharpness"),
                H("Root-pulse sharpness certificate"),
                StatementSource.FromAuthor(SharpnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every chain size n at least two, the state carrier is Fin n. "
                            + "The update is constructed as truncated predecessor and the "
                            + "Boolean readout is true exactly at state zero. The displayed "
                            + "distance is the repository separationTime for those maps.")),
                    Paragraph(Text(
                        "If i is below j, both readouts remain false before time i, while at "
                            + "time i the first trajectory reaches the root and the second does "
                            + "not. Pinned Mathlib's Nat.find_eq_iff therefore gives d_q(i,j)=i. "
                            + "The penultimate and last states supply the endpoint certificate.")),
                    Paragraph(Text(
                        "At depth m, two distinct states remain related exactly when both lie "
                            + "strictly above m. Hence consecutive observation relations refine "
                            + "strictly exactly for m<n-2. The existing least-stability test and "
                            + "finite supremum then both evaluate to n-2.")),
                    Paragraph(Text(
                        "The repository theorem finite_observation_refinement_and_stability_bound "
                            + "is applied to the surjective root readout. Its two final inequalities "
                            + "give the general class-count bound, and the constructed chain attains "
                            + "that bound because the Boolean readout has two values."))),
                DescribeRole.Theorem))));

    private static Formula Call(Formula function, params Formula[] arguments)
    {
        var content = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula Cardinality(Formula value) =>
        Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula SharpnessFormula()
    {
        Formula n = F.Id("n");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula m = F.Id("m");
        Formula distance = new Formula.Subscript(F.Id("d"), F.Id("q"));
        Formula relation = new Formula.Subscript(F.Id("E"), m);
        Formula successorRelation = new Formula.Subscript(
            F.Id("E"), Seq(m, Plus, D(1)));
        Formula stableDepth = new Formula.Subscript(F.Id("m"), Star);
        Formula maximumDistance = new Formula.Subscript(F.Id("d"), F.Id("max"));
        Formula chainBound = Seq(n, Minus, D(2));
        Formula stateCount = Cardinality(
            Seq(Operatorname, Grp(F.Id("Fin")), Open, n, Close));
        Formula outputCount = Cardinality(F.Id("Bool"));
        Formula generalBound = Seq(stateCount, Minus, outputCount);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(2), Sp, Leq, Sp, n, Sp, Rightarrow, RowBreak,
            Open, Forall, Sp, i, Comma, Sp, j, Comma, Sp,
            D(0), Sp, Leq, Sp, i, Sp, Lt, Sp, j, Sp, Leq, Sp,
            n, Minus, D(1), Comma, Sp,
            Call(distance, i, j), Sp, Eq, Sp, i, Close, Sp, Land, RowBreak,
            Call(distance, Seq(n, Minus, D(2)), Seq(n, Minus, D(1))), Sp,
            Eq, Sp, chainBound, Sp, Land, RowBreak,
            Open, Forall, Sp, m, Comma, Sp,
            successorRelation, Sp, Subset, Sp, relation, Sp, Iff, Sp,
            m, Sp, Lt, Sp, chainBound, Close, Sp, Land, RowBreak,
            stableDepth, Sp, Eq, Sp, chainBound, Sp, Land, RowBreak,
            maximumDistance, Sp, Eq, Sp, chainBound, Sp, Land, RowBreak,
            stableDepth, Sp, Leq, Sp, generalBound, Sp, Land, RowBreak,
            stableDepth, Sp, Eq, Sp, generalBound, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
