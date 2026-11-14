using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal;

internal sealed class CyclicArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic residue selection without enumeration",
        H("Discrete interval and no-carry tools for the diagonal"),
        Blocks(
            Describe.Lean(DescribeId.Create("helper-cyclic-arithmetic-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleDiagonal/CyclicArithmetic.cyclic_cover"),
                H("Hit a permitted residue interval"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For G>=2,m>=2 and (2Gm+1) not dividing tau, cyclic_cover constructs integers n,l with -2G<=n<2G, Gm-m<=l<=Gm-2 and divisibility of tau+Gm-1+nm-l. euclidean_gap_hit supplies the discrete gap argument, including its excluded residue; no real rotation or sampled orbit is used."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("helper-cyclic-arithmetic-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleDiagonal/CyclicArithmetic.equality_residue"),
                H("Equality residue including the wrap"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For g>=1 the shifted residue interval -1<=n<g contains a solution to (g+1) dividing tau+1+n. odd_successor_not_dvd_pow excludes divisibility of a power of two by 2^c+1 for c>=1. native_hr recovers native h,r and scaled_rectangle interpolates the separately affine h,r margins. These facts are consumed by GeneralArithmetic.selected_rectangle."))), DescribeRole.Lemma),
            Paragraph(Text("These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1."))), []));
}
