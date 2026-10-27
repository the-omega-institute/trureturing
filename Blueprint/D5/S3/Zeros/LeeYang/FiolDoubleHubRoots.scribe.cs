using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.LeeYang;

internal sealed class FiolDoubleHubRootsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The physical double-hub family: roots.",
        H("Double-hub roots"), Blocks(
            Paragraph(Text("The corrected samples yield N distinct upper roots of Q. Their conjugates give N distinct lower roots, exhausting its degree 2N. The complete root multiset is the sum of those two families and is duplicate free.")),
            Paragraph(Text("For R_m, add exactly h copies of 1. Its other roots are simple and have norm 1. The multiplicity at 1 is 2m+2 for even m and 2m for odd m. The number of other roots is 2m+4 for even m and 2m+6 for odd m.")),
            Paragraph(Text("These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.")),
            Describe.Lean(DescribeId.Create("fioldoublehubroots-corrected-samples"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.corrected_samples"), H("corrected samples"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Constructs the complete strictly ordered alternating sample family for every d>=2 and every residue. Exact source statement: theorem corrected_samples (d : \u2115) (hd : 2\u2264d) :     \u2203 s : \u2115 \u2192 \u211d, s 0=0 \u2227 s (N d)=Real.pi \u2227       (\u2200 k, k<N d \u2192 s k<s (k+1)) \u2227       (\u2200 k, k\u2264N d \u2192 0<(-1:\u211d)^k*(phaseValue d (s k)).re)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fioldoublehubroots-q-complete-roots"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.Q_complete_roots"), H("Q complete roots"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Combines the corrected family with actual degree exhaustion for a full simple root multiset. Exact source statement: theorem Q_complete_roots (d : \u2115) (hd : 2\u2264d) :     \u2203 theta : Fin (N d) \u2192 \u211d, StrictMono theta \u2227       (\u2200 j, 0<theta j \u2227 theta j<Real.pi) \u2227       ((Q d).map Complex.ofRealHom).roots =         Finset.univ.val.map (fun j => Complex.exp ((theta j:\u2102)*Complex.I)) +         Finset.univ.val.map (fun j => star (Complex.exp ((theta j:\u2102)*Complex.I))) \u2227       ((Q d).map Complex.ofRealHom).roots.Nodup."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fioldoublehubroots-candidate-full-root-multiset"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.candidate_full_root_multiset"), H("candidate full root multiset"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Derives the exact R multiset using its independent factorization. Exact source statement: theorem candidate_full_root_multiset (m : \u2115) (hm : 1\u2264m) :     \u2203 theta : Fin (N (m+1)) \u2192 \u211d, StrictMono theta \u2227       (\u2200j,0<theta j \u2227 theta j<Real.pi) \u2227       ((R m).map Complex.ofRealHom).roots =         Multiset.replicate (h (m+1)) 1 +         Finset.univ.val.map (fun j => Complex.exp ((theta j:\u2102)*Complex.I)) +         Finset.univ.val.map (fun j => star (Complex.exp ((theta j:\u2102)*Complex.I))) \u2227       ((Q (m+1)).map Complex.ofRealHom).roots.Nodup."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fioldoublehubroots-candidate-nonunit-root-multiplicity"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.candidate_nonunit_root_multiplicity"), H("candidate nonunit root multiplicity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transfers exhaustive Q simplicity to each non1 R root and proves its norm. Exact source statement: theorem candidate_nonunit_root_multiplicity (m : \u2115) (hm : 1\u2264m) (z : \u2102)     (hz : ((R m).map Complex.ofRealHom).IsRoot z) (hz1 : z\u22601) :     Polynomial.rootMultiplicity z ((R m).map Complex.ofRealHom)=1 \u2227 \u2016z\u2016=1."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fioldoublehubroots-candidate-other-roots-card"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubRoots.candidate_other_roots_card"), H("candidate other roots card"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Counts the complete filtered R multiset with both parities. Exact source statement: theorem candidate_other_roots_card (m : \u2115) (hm : 1\u2264m) :     (((R m).map Complex.ofRealHom).roots.filter (fun z => z\u22601)).card =       if Even m then 2*m+4 else 2*m+6."))), DescribeRole.Theorem))));
}
