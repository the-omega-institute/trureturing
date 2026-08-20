using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints;

internal sealed class FiniteContractingStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite contracting set updates stabilize with a sharp strict-change bound.",
        H("Finite Contracting Stability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-contracting-updates-stabilize"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/FiniteContractingStability."
                        + "finite_contracting_updates_stabilize"),
                H("Finite contracting updates stabilize"),
                StatementSource.FromAuthor(StabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be finite, let U map subsets of X to subsets of X without "
                            + "adding states, and let S satisfy S(n+1) = U(S(n)). There is an "
                            + "index N, no larger than the cardinality of S(0), after which "
                            + "every set in the sequence equals S(N).")),
                    Paragraph(Text(
                        "The set of all indices at which the update is strict has cardinality "
                            + "at most the cardinality of S(0). Thus the statement records both "
                            + "eventual stability and the source's strict-change bound.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Nat.stabilises_of_antitone for the cardinality "
                            + "sequence. Equal consecutive cardinalities force equal finite "
                            + "sets, and all strict changes occur before the resulting stable "
                            + "index. Repository search found no generic theorem containing "
                            + "both conclusions."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

    private static Formula SetOf(Formula type) =>
        Apply(Seq(Operatorname, Grp(F.Id("Set"))), type);

    private static Formula Ncard(Formula set) =>
        Apply(Seq(Operatorname, Grp(F.Id("ncard"))), set);

    private static Formula StabilityFormula()
    {
        Formula carrier = F.Id("X");
        Formula update = F.Id("U");
        Formula sequence = F.Id("S");
        Formula subset = F.Id("A");
        Formula index = F.Id("n");
        Formula stableIndex = F.Id("N");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula carrierSets = SetOf(carrier);
        Formula initial = Apply(sequence, D(0));
        Formula current = Apply(sequence, index);
        Formula successor = Apply(sequence, Seq(index, Plus, D(1)));
        Formula stable = Apply(sequence, stableIndex);
        Formula changeSet = Seq(
            OpenBrace, index, InMacro, Sp, naturals, Sp, Mid, Sp,
            successor, Sp, Neq, Sp, current, CloseBrace);

        return Disp(Seq(
            Forall, Sp, carrier, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            Typeclass("Finite", carrier), Comma, Esc,
            update, Colon, Sp, carrierSets, Sp, To, Sp, carrierSets, Comma, Esc,
            Open, Forall, Sp, subset, Colon, Sp, carrierSets, Comma, Sp,
            Apply(update, subset), Sp, Subseteq, Sp, subset, Close, Comma, Esc,
            sequence, Colon, Sp, naturals, Sp, To, Sp, carrierSets, Comma, Esc,
            Open, Forall, Sp, index, Colon, Sp, naturals, Comma, Sp,
            successor, Sp, Eq, Sp, Apply(update, current), Close, Sp,
            Rightarrow, RowBreak,
            Open, Exists, Sp, stableIndex, InMacro, Sp, naturals, Comma, Sp,
            stableIndex, Sp, Leq, Sp, Ncard(initial), Sp, Land, Sp,
            Forall, Sp, index, InMacro, Sp, naturals, Comma, Sp,
            stableIndex, Sp, Leq, Sp, index, Sp, Rightarrow, Sp,
            current, Sp, Eq, Sp, stable, Close, Sp, Land, RowBreak,
            Ncard(changeSet), Sp, Leq, Sp, Ncard(initial), Dot));
    }
}
