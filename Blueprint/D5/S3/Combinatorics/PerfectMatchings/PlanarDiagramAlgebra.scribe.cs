using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class PlanarDiagramAlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal planar diagram algebra", H("The literal planar diagram algebra"), Blocks(
            Paragraph(Text("A commutative coefficient ring R is arbitrary. Diagram(n) contains all boundary matchings admitting an NCMatching representative, without identifying distinct pairings. TL(R,n) is the free R-module on that set. The MonoidAlgebra wrapper supplies only coefficients and additive structure: no multiplication is installed on Diagram(n). The multiplication here is the bilinear extension of the loop-zero product. It is associative by the actual matching loop cocycle. The coefficient rings Z and C use the same construction. Fin(n-1) is empty at n=0 and n=1.")),
            Describe.Lean(DescribeId.Create("diagram"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.Diagram"),
                H("Diagram"), StatementSource.FromAuthor(Disp(All("n", Id("Nat"), Equal(Call("Diagram", Id("n")), Call("Subtype", Call("Matching", Call("Boundary", Id("n"))), Call("HasNoncrossingRepresentative", Id("n"))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("HasNoncrossingRepresentative(d) means that there exists M:NCMatching(2*n) with toMatching(M)=d."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tl"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.TL"),
                H("TL"), StatementSource.FromAuthor(Disp(RingAll("R", All("n", Id("Nat"), Equal(Call("TL", Id("R"), Id("n")), Call("MonoidAlgebra", Id("R"), Call("Diagram", Id("n")))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The carrier is exactly the finite-support coefficient functions on all diagrams, in a one-field wrapper."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("additivewithone"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.additiveWithOne"),
                H("additiveWithOne"), StatementSource.FromAuthor(Disp(RingAll("R", All("n", Id("Nat"), Equal(Call("additiveWithOne", Id("R"), Id("n")), Call("AdditiveGroupWithUnit", Call("FiniteSupportAddition", Call("Diagram", Id("n")), Id("R")), Call("single", Call("IdentityDiagram", Id("n")), Num(1)))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Addition and negation are coefficientwise, and the unit is the single identity diagram with coefficient one. Natural and integer casts are the canonical additive casts."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ring"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.ring"),
                H("ring"), StatementSource.FromAuthor(Disp(RingAll("R", All("n", Id("Nat"), Equal(Call("ring", Id("R"), Id("n")), Call("RingStructure", Call("TL", Id("R"), Id("n")), Call("BilinearExtension", Call("LoopZeroProduct", Id("n"))), Call("single", Call("IdentityDiagram", Id("n")), Num(1)))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The additive structure is unchanged. Basis products use composite(d,e) with coefficient zero for any internal loop; the loop cocycle proves their associativity. Linear extension proves the full ring laws."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("algebra"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.algebra"),
                H("algebra"), StatementSource.FromAuthor(Disp(RingAll("R", All("n", Id("Nat"), Equal(Call("algebra", Id("R"), Id("n")), Call("AlgebraFromModule", Call("TL", Id("R"), Id("n")), Call("CoefficientwiseScalarAction", Id("R")), Call("algebraMap", Id("R"), Call("TL", Id("R"), Id("n"))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The algebra map sends r to r times the unit; the existing coefficientwise R-module structure is compatible with multiplication on both sides."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("single-mul-single"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.single_mul_single"),
                H("single_mul_single"), StatementSource.FromAuthor(Disp(RingAll("R", All("n", Id("Nat"), All("a", Call("Diagram", Id("n")), All("b", Call("Diagram", Id("n")), All("r", Id("R"), All("s", Id("R"), Equal(Call("Multiply", Call("single", Id("a"), Id("r")), Call("single", Id("b"), Id("s"))), Call("If", Equal(Call("internalLoopCount", Call("val", Id("a")), Call("val", Id("b"))), Num(0)), Call("single", Call("PlanarComposite", Id("a"), Id("b")), Call("Multiply", Id("r"), Id("s"))), Num(0))))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("PlanarComposite carries exactly composite(val(a),val(b)), with planarity supplied by composite_planar. This is the defining vertical concatenation rule for arbitrary coefficients."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("generator"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.generator"),
                H("generator"), StatementSource.FromAuthor(Disp(RingAll("R", All("n", Id("Nat"), All("i", Call("Fin", Call("Subtract", Id("n"), Num(1))), Equal(Call("generator", Id("R"), Id("n"), Id("i")), Call("single", Call("PlanarCupcap", Id("n"), Id("i")), Num(1)))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("PlanarCupcap is cupcapMatching at the zero-based index; cupcap_planar provides its noncrossing witness. The printed generator label is i+1."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("h"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.h"),
                H("h"), StatementSource.FromAuthor(Disp(RingAll("R", All("n", Id("Nat"), Equal(Call("h", Id("R"), Id("n")), Call("Negate", Call("Sum", Call("Fin", Call("Subtract", Id("n"), Num(1))), Call("generator", Id("R"), Id("n"))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("This is the negative sum of the n-1 standard open-boundary generators."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("instmultl"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.instMulTL"),
                H("instMulTL"), StatementSource.FromAuthor(Disp(RingAll("R", All("n", Id("Nat"), All("a", Call("TL", Id("R"), Id("n")), All("b", Call("TL", Id("R"), Id("n")), Equal(Call("Multiply", Id("a"), Id("b")), Call("bilinear", Id("a"), Id("b"))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The multiplication field sends (a,b) to bilinear(a)(b). Bilinear is the two successive Finsupp lifts of basisProduct(d,e): one composite basis vector when the internal loop count is zero, and zero otherwise."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("instonetl"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/PlanarDiagramAlgebra.instOneTL"),
                H("instOneTL"), StatementSource.FromAuthor(Disp(RingAll("R", All("n", Id("Nat"), Equal(Call("One", Call("TL", Id("R"), Id("n"))), Call("single", Call("identity", Id("n")), Num(1))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Identity(n) is identityMatching(n) equipped with the noncrossing witness identity_planar(n)."))), DescribeRole.Definition))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula RingAll(string name, Formula body) => All(name, Id("Type"), Seq(OpenBracket, Call("CommRing", Id(name)), CloseBracket, Sp, body));
}
