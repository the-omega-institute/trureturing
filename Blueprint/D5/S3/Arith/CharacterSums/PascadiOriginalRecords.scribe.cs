using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiOriginalRecordsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/pascadi2025nonabelianamplification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed good record has uniformly O(p^epsilon) actual reduced physical basis realizations in the long simple-root chart. The proof consumes the original word equations and congruence lattice, reconstructs the actual product R1 R2, and proves uniqueness of V from the intrinsic pair (beta,R). Exceptional records and summation over records remain outside this theorem.",
        H("Actual realizations of one good record"),
        Blocks(
            Paragraph(Text("Fix the prime p, the literal anchor coordinate q, the baseline endpoint pair, a second endpoint pair, the original fixed units a1,a2 modulo c=p^3, and positive scales X<=Y with 3Y<p^2. GoodRecordRealization ranges over actual integer pairs of physical basis vectors (R,V). Its hypotheses require an oriented reduced basis of the congruence lattice with literal middle letters t=-(physical R V q)2 and w=-(physical R V q)1, the long condition c^2<XY Q(R), unit t and R1, original word solutions at both endpoint pairs, unit baseline first coordinates, and a nonzero derivative modulo p of the actual pencil at beta=V1/R1. These are explicit chart conditions; their coverage of all original solutions is not asserted.")),
            Paragraph(Text("The original endpoint identity gives alpha L(beta)+Q(beta)=0. Unit baseline physical coordinates make Q(beta) and then L(beta) units, so the fixed record reconstructs alpha=-Q/L. Combining the anchor identity R1(q1+beta q2)=-w with w R2=t R1 and alpha a1 a2 t R1=-1 gives (a1 a2 alpha(q1+beta q2))(R1 R2)=1. Thus recordProduct is the actual residue of R1 R2, without assuming a product supplier.")),
            Paragraph(Text("The determinant-one weighted metric gives 2|R1 R2|<=Q(R), while reduction gives Q(R)<2c. The lattice relation and the unit hypotheses imply R2 is a unit too, so 0<|R1 R2|<c. If n is the least nonnegative representative of recordProduct, the integer product can only be n or n-c. Their signed divisorsAntidiag sets therefore contain every possible actual R.")),
            Paragraph(Text("The long condition and Q(V)Q(R)<=2c^2 imply Q(V)<2XY and |V1|<3X/2. Equal intrinsic beta and R give equal V1 modulo c; the difference is smaller than 3X<=3Y<p^2<c, hence the integer coordinates agree. The determinant-c equation then forces V2 to agree. This proves injectivity for the actual physical bases, rather than including uniqueness in their definition.")),
            Paragraph(Text("A simple root modulo p has at most one lift to a root modulo p^3: a nilpotent difference between two roots is annihilated by a unit Taylor factor. The actual degree-three pencil consequently has at most three simple prime-cube roots, including the empty case when its reduction is zero. For each beta there are two signed factor sets with product absolute value at most p^3. The existing signed divisor estimate at exponent epsilon/3 bounds each by C p^epsilon, so all actual physical realizations number at most 6C p^epsilon. The constant is independent of the prime, scales, original units and fixed record.")),
            Describe.Lean(DescribeId.Create("pascadi-original-records-beta"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalRecords.recordBeta"),
                H("Intrinsic physical ratio"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The ratio of the actual first basis coordinates modulo c."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pascadi-original-records-alpha"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalRecords.recordAlpha"),
                H("Coefficient recovered from the baseline"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The total residue expression -Q(beta)/L(beta), proved to agree with the original word coefficient on actual good realizations."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pascadi-original-records-product"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalRecords.recordProduct"),
                H("Recovered physical product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The inverse of a1 a2 alpha(q1+beta q2), proved from the original word and lattice equations to equal R1 R2 modulo c."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pascadi-original-records-realization"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalRecords.GoodRecordRealization"),
                H("Actual physical good-record realization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A predicate on actual integer basis pairs, retaining the original word equations, reduced physical congruence basis, longness, unit hypotheses and the simple derivative condition."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pascadi-original-records-subpower"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalRecords.actual_good_record_realizations_subpower"),
                H("Uniform subpower count of actual good-record realizations"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every positive epsilon, a constant C bounds the finite number of all actual reduced physical bases realizing any fixed good record by C p^epsilon, under 0<X<=Y and 3Y<p^2. This closes fixed-record multiplicity on the stated long simple-root chart; it does not count exceptional charts or sum over all records."))), DescribeRole.Theorem)),
        edges: []));
}
