using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Negation;

internal sealed class PolyploidAlleleComplementarityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Negation/PolyploidAlleleComplementarity."
            + "polyploid_allele_events_overlap_and_haploid_complement";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mixed polyploid genotypes obstruct Boolean allele complementarity.",
        H("Polyploid Allele Complementarity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("polyploid-allele-events-overlap-and-haploid-complement"),
                DeclarationHandle.Create(Declaration),
                H("Allele events overlap exactly beyond haploidy"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A biallelic p-copy genotype is a function from Fin(p) to Bool. "
                            + "For p at least two, an explicit mixed genotype has one false "
                            + "locus and one true locus, so both allele-presence events occur.")),
                    Paragraph(Text(
                        "For every nonempty genotype carrier, the true-allele event is the "
                            + "set complement of the false-allele event exactly when p equals "
                            + "one. At higher ploidy the same mixed genotype prevents equality.")),
                    Paragraph(Text(
                        "The predicates and their carrier are displayed directly; no genotype "
                            + "event is defined in terms of the claimed intersection or "
                            + "complement relation."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula p = F.Id("p");
        Formula genotype = F.Id("g");
        Formula locus = F.Id("i");
        Formula nat = F.Id("Nat");
        Formula finP = Call("Fin", p);
        Formula genotypeType = Seq(finP, Sp, To, Sp, F.Id("Bool"));

        Formula Event(Formula allele) => Seq(
            OpenBrace, genotype, Colon, Sp, genotypeType, Sp, Mid, Sp,
            Exists, Sp, locus, Colon, Sp, finP, Comma, Sp,
            Call("apply", genotype, locus), Sp, Eq, Sp, allele,
            CloseBrace);

        Formula alleleA = Event(F.Id("false"));
        Formula alleleB = Event(F.Id("true"));

        Formula overlapClause = Seq(
            Open, Forall, Sp, p, Colon, Sp, nat, Comma, Sp,
            D(2), Sp, Leq, Sp, p, Sp, Rightarrow, Sp,
            Call("Nonempty", Call("intersection", alleleA, alleleB)), Close);

        Formula complementClause = Seq(
            Open, Forall, Sp, p, Colon, Sp, nat, Comma, Sp,
            D(1), Sp, Leq, Sp, p, Sp, Rightarrow, Sp,
            Open, alleleB, Sp, Eq, Sp, Call("complement", alleleA),
            Sp, Iff, Sp, p, Sp, Eq, Sp, D(1), Close, Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            overlapClause, Sp, Land, RowBreak, Grp(),
            complementClause, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
