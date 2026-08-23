using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Descent;

internal sealed class FiniteSelfMapConjugacyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjugacy preserves cycle counts, and cycle type completely classifies finite permutations.",
        H("Finite Self-Map Conjugacy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conjugacy-preserves-cycle-length-multiplicities"),
                DeclarationHandle.Create(
                    "D5/S1/Descent/FiniteSelfMapConjugacy.finite_self_map_conjugacy"),
                H("Conjugacy preserves every cycle-length multiplicity"),
                StatementSource.FromAuthor(ConjugacyInvariantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An equivalence that intertwines two finite self-maps carries every "
                            + "iterate of the first map to the corresponding iterate of the "
                            + "second. It therefore preserves the minimal period of each point.")),
                    Paragraph(Text(
                        "For every natural number n, the relabeling restricts to a bijection "
                            + "between the points of minimal period n. The two filtered finite "
                            + "sets have the same cardinality, so dividing by n gives equal "
                            + "cycle-length multiplicities. At n = 0 both multiplicities are "
                            + "zero, and transient points do not contribute.")),
                    Paragraph(Text(
                        "This is an invariance statement for arbitrary finite self-maps, not a "
                            + "classification theorem: cycle counts do not record the transient "
                            + "trees attached to the cycles."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cycle-type-completely-classifies-finite-permutations"),
                DeclarationHandle.Create(
                    "D5/S1/Descent/FiniteSelfMapConjugacy.permutation_cycle_type_complete"),
                H("Cycle type completely classifies finite permutations"),
                StatementSource.FromAuthor(PermutationCompletenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two permutations of the same finite set have equal cycle type exactly "
                            + "when a permutation of the underlying set relabels one into the "
                            + "other. The relabeling is exhibited explicitly and intertwines "
                            + "the two permutation actions pointwise.")),
                    Paragraph(Text(
                        "Because a permutation has no transient points, its cycle decomposition "
                            + "contains the whole dynamical system. Thus cycle type is a complete "
                            + "conjugacy invariant in the permutation case, in contrast with the "
                            + "one-way invariant for general finite self-maps."))),
                DescribeRole.Theorem))));

    private static Formula ConjugacyInvariantFormula()
    {
        Formula carrierY = F.Id("Y");
        Formula carrierZ = F.Id("Z");
        Formula tau = F.Id("tau");
        Formula sigma = F.Id("sigma");
        Formula relabel = F.Id("relabel");
        Formula length = F.Id("n");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));

        return Disp(Seq(
            Forall, Sp, carrierY, Comma, Sp, carrierZ, Colon, Sp, type, Comma, Esc,
            OpenBracket, Call("Fintype", carrierY), CloseBracket, Comma, Sp,
            OpenBracket, Call("Fintype", carrierZ), CloseBracket, Comma, Esc,
            tau, Colon, Sp, carrierY, Sp, To, Sp, carrierY, Comma, Sp,
            sigma, Colon, Sp, carrierZ, Sp, To, Sp, carrierZ, Comma, Esc,
            relabel, Colon, Sp, carrierY, Sp, Equiv, Sp, carrierZ, Comma, Esc,
            Call("Conjugates", tau, sigma, relabel), Sp, Rightarrow, Sp,
            Forall, Sp, length, Sp, InMacro, Sp, naturals, Comma, Esc,
            Call("cycleLengthMultiplicity", tau, length), Sp, Eq, Sp,
            Call("cycleLengthMultiplicity", sigma, length), Dot));
    }

    private static Formula PermutationCompletenessFormula()
    {
        Formula carrier = F.Id("Y");
        Formula tau = F.Id("tau");
        Formula sigma = F.Id("sigma");
        Formula relabel = F.Id("relabel");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula permutation = Call("Perm", carrier);

        return Disp(Seq(
            Forall, Sp, carrier, Colon, Sp, type, Comma, Esc,
            OpenBracket, Call("Fintype", carrier), CloseBracket, Comma, Sp,
            OpenBracket, Call("DecidableEq", carrier), CloseBracket, Comma, Esc,
            tau, Comma, Sp, sigma, Colon, Sp, permutation, Comma, Esc,
            Call("cycleType", tau), Sp, Eq, Sp, Call("cycleType", sigma), Sp,
            Iff, Sp, Exists, Sp, relabel, Colon, Sp, permutation, Comma, Esc,
            Call("Conjugates", tau, sigma, relabel), Dot));
    }
}
