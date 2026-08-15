using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting.MiuSystem;

internal sealed class ReachabilityInvariantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "MIU derivability has exactly two I-count residues modulo three and excludes MU.",
        H("MIU Reachability Invariant"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("miu-reachable-residues-and-mu-exclusion"),
                DeclarationHandle.Create(
                    "D5/S0/Rewriting/MiuSystem/ReachabilityInvariant."
                    + "miu_observation_invariant_clauses"),
                H("Reachable residues and MU exclusion"),
                StatementSource.FromAuthor(InvariantClausesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem is stated directly over pinned mathlib's Miu.Miustr and "
                        + "Miu.Derivable notions. That archived development defines the MIU axiom "
                        + "and all four production rules.")),
                    Paragraph(Text(
                        "The proof applies mathlib's necessary-condition theorem: every derivable "
                        + "word has I-count congruent to one or two modulo three. Thus the count is "
                        + "never zero modulo three, without any bounded enumeration.")),
                    Paragraph(Text(
                        "Both residues occur: MI witnesses residue one, and one application of the "
                        + "tail-duplication rule derives MII and witnesses residue two. The final "
                        + "conjunct applies mathlib's theorem that MU is not derivable.")),
                    Paragraph(Text(
                        "This result does not assert the separate bounded-BFS cardinality 216. "
                        + "Pure kernel evaluation of that finite computation exceeded the measured "
                        + "elaboration budget, while native evaluation would enlarge the permitted "
                        + "axiom closure, so that numerical clause remains open."))),
                DescribeRole.Theorem))));

    private static Formula Derivable(Formula word) =>
        Seq(Operatorname, Grp(F.Id("Miu.Derivable")), Open, word, Close);

    private static Formula ICountModThree(Formula word) =>
        new Formula.Modulo(
            Seq(F.Id("count_I"), Open, word, Close),
            D(3));

    private static Formula InvariantClausesFormula()
    {
        Formula word = F.Id("w");
        Formula residue = F.Id("r");
        Formula words = Seq(Mathcal, Grp(F.Id("W")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        return Disp(Seq(
            Open,
            Forall, Sp, word, InMacro, Sp, words, Comma, Esc,
            Derivable(word), Sp, Rightarrow, Sp,
            ICountModThree(word), Sp, Neq, Sp, D(0),
            Close, Sp, Land, Sp,
            Open,
            Forall, Sp, residue, InMacro, Sp, naturals, Comma, Esc,
            Open,
            Open,
            Exists, Sp, word, InMacro, Sp, words, Comma, Esc,
            Derivable(word), Sp, Land, Sp,
            ICountModThree(word), Sp, Eq, Sp, residue,
            Close, Sp, Iff, Sp,
            residue, Sp, Eq, Sp, D(1), Sp, Lor, Sp,
            residue, Sp, Eq, Sp, D(2),
            Close,
            Close, Sp, Land, Sp,
            Neg, Sp, Derivable(F.Id("MU")), Dot));
    }
}
