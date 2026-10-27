using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.LeeYang;

internal sealed class FiolDoubleHubPhysicalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The physical double-hub family: physical.",
        H("Double-hub physical"), Blocks(
            Paragraph(Text("For every m>=1 and cutoff>=3, the roots and multiplicities are those of the coefficient extracted from the original physical source. The coefficient identity supplies the nonzero scalar relating that source to R_m; scalar multiplication preserves the complete root multiset, every root predicate and every multiplicity.")),
            Paragraph(Text("There is a strictly increasing list of N upper angles in (0,pi). The actual physical coefficient has precisely their exponentials, their conjugates, and h copies of 1. Every other root is simple with norm 1. The point -1 is absent. The points i and -i occur exactly for m mod 4 equal to 1, each with multiplicity one.")),
            Paragraph(Text("The independent homogeneous identity holds at arbitrary complex a,b. Both punctured coordinate axes have nonzero value, and the origin has value zero. Thus neither projective axis adds a missing zero to the ratio description. The result concerns this infinite family and this assignment-summed formal coefficient at tau=-1; it does not establish the conjecture for all trees or for a fixed labelled placement.")),
            Paragraph(Text("These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.")),
            Describe.Lean(DescribeId.Create("fioldoublehubphysical-spintruncation"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubPhysical.spinTruncation"), H("spinTruncation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This defines spinTruncation for the physical double-hub family."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fioldoublehubphysical-spincoefficient"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubPhysical.spinCoefficient"), H("spinCoefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This defines spinCoefficient for the physical double-hub family."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fioldoublehubphysical-spin-coefficient-eq-source"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubPhysical.spin_coefficient_eq_source"), H("spin coefficient eq source"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Connects two independently defined formal coefficients through the spin-sign proof. Exact source statement: theorem spin_coefficient_eq_source (m cutoff : \u2115) :     spinCoefficient m cutoff = sourceCoefficient m cutoff."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fioldoublehubphysical-physical-root-classification"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubPhysical.physical_root_classification"), H("physical root classification"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Uses the actual spin/source bridge and nonzero normalization to transfer complete root/multiplicity classification. Exact source statement: theorem physical_root_classification (m cutoff : \u2115) (hm : 1 \u2264 m) (hc : 3 \u2264 cutoff) :     let p := (spinCoefficient m cutoff).map Complex.ofRealHom     p.natDegree = 4*m+6 \u2227 p \u2260 0 \u2227     \u2203 theta : Fin (N (m+1)) \u2192 \u211d, StrictMono theta \u2227       (\u2200 j, 0 < theta j \u2227 theta j < Real.pi) \u2227       p.roots = Multiset.replicate (h (m+1)) 1 +         Finset.univ.val.map (fun j => Complex.exp ((theta j:\u2102)*Complex.I)) +         Finset.univ.val.map (fun j => star (Complex.exp ((theta j:\u2102)*Complex.I))) \u2227       Polynomial.rootMultiplicity 1 p = (if Even m then 2*m+2 else 2*m) \u2227       (\u2200 z : \u2102, p.IsRoot z \u2192 z \u2260 1 \u2192         Polynomial.rootMultiplicity z p = 1 \u2227 \u2016z\u2016 = 1) \u2227       (p.roots.filter (fun z => z \u2260 1)).card = (if Even m then 2*m+4 else 2*m+6) \u2227       \u00ac p.IsRoot (-1) \u2227       (p.IsRoot Complex.I \u2194 m % 4 = 1) \u2227       (p.IsRoot (-Complex.I) \u2194 m % 4 = 1) \u2227       (m % 4 = 1 \u2192 Polynomial.rootMultiplicity Complex.I p = 1 \u2227         Polynomial.rootMultiplicity (-Complex.I) p = 1)."))), DescribeRole.Theorem))));
}
