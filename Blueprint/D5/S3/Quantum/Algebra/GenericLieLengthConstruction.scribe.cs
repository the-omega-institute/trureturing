using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class GenericLieLengthConstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Algebra/GenericLieLengthConstruction.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-colour anchored binary heap produces a logarithmic-length generating pair.",
        H("GenericLieLengthConstruction"),
        Blocks(
            Describe.Lean(DescribeId.Create("jc-genericlielengthconstruction-heapcolor"),
                DeclarationHandle.Create(Prefix + "heapColor"), H("heapColor"),
                StatementSource.FromAuthor(Formula0()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Three colours distinguish a parent from each child and distinguish its two children. Nat.div and Nat.mod are natural quotient and remainder."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthconstruction-energy"),
                DeclarationHandle.Create(Prefix + "energy"), H("energy"),
                StatementSource.FromAuthor(Formula1()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The distinguished zero vertex has energy 7; the three heap colours have energies 0, 1 and 3."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthconstruction-heapedge"),
                DeclarationHandle.Create(Prefix + "heapEdge"), H("heapEdge"),
                StatementSource.FromAuthor(Formula2()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The anchor edge joins zero to one, and every other edge joins a positive vertex to its binary-heap parent."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthconstruction-meanenergy"),
                DeclarationHandle.Create(Prefix + "meanEnergy"), H("meanEnergy"),
                StatementSource.FromAuthor(Formula3()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Subtracting the mean makes the diagonal trace zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthconstruction-centeredenergy"),
                DeclarationHandle.Create(Prefix + "centeredEnergy"), H("centeredEnergy"),
                StatementSource.FromAuthor(Formula4()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("These centered complex entries are real-valued."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthconstruction-a"),
                DeclarationHandle.Create(Prefix + "A"), H("A"),
                StatementSource.FromAuthor(Formula5()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first Hermitian generator is the centered energy diagonal."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthconstruction-b"),
                DeclarationHandle.Create(Prefix + "B"), H("B"),
                StatementSource.FromAuthor(Formula6()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The second Hermitian generator is the symmetric adjacency matrix of the anchored heap."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthconstruction-gen"),
                DeclarationHandle.Create(Prefix + "gen"), H("gen"),
                StatementSource.FromAuthor(Formula7()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two-entry vector lists the diagonal and adjacency generators."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthconstruction-igen"),
                DeclarationHandle.Create(Prefix + "iGen"), H("iGen"),
                StatementSource.FromAuthor(Formula8()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Multiplication by the complex imaginary unit gives traceless skew-Hermitian generators."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthconstruction-anchored-units-mem"),
                DeclarationHandle.Create(Prefix + "anchored_units_mem"), H("anchored_units_mem"),
                StatementSource.FromAuthor(Formula9()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Degree-seven Lagrange polynomials in the diagonal adjoint select gaps from {−7,−3,−2,−1,1,2,3,7}. The anchor units then propagate to both children in eight additional letters per level. Nat.size is the binary length, zero at zero and 1 + Nat.log 2 v for positive v."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jc-genericlielengthconstruction-suliering"),
                DeclarationHandle.Create(Prefix + "suLieRing"), H("suLieRing"),
                StatementSource.FromAuthor(Formula10()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Lie-ring structure on the real submodule is the one on the corresponding Lie subalgebra."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthconstruction-suliealgebra"),
                DeclarationHandle.Create(Prefix + "suLieAlgebra"), H("suLieAlgebra"),
                StatementSource.FromAuthor(Formula11()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real Lie-algebra structure is inherited from the same Lie subalgebra."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthconstruction-compactpair"),
                DeclarationHandle.Create(Prefix + "compactPair"), H("compactPair"),
                StatementSource.FromAuthor(Formula12()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("compactPair has type Fin 2 → suSet (n + 2), with value iGen n i. Its subtype property is exactly traceless skew-Hermiticity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("jc-genericlielengthconstruction-rightspan-map"),
                DeclarationHandle.Create(Prefix + "rightSpan_map"), H("rightSpan_map"),
                StatementSource.FromAuthor(Formula13()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A Lie homomorphism commutes with every word evaluation and hence with its span."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jc-genericlielengthconstruction-compactpair-span-top"),
                DeclarationHandle.Create(Prefix + "compactPair_span_top"), H("compactPair_span_top"),
                StatementSource.FromAuthor(Formula14()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Bracketing the anchored matrix units gives all adjusted units, which span the trace kernel. Scaling by the imaginary unit and taking skew-adjoint parts gives the whole real subalgebra."))), DescribeRole.Theorem)),
        []));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Formula0() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("heapColor"), Sp, F.Id("v"), Sp, Eq, Sp, Named("if"), Sp, F.Id("v"), Sp, Leq, Sp, D(1), Sp, Named("then"), Sp, D(0), Sp, Named("else"), Sp, Named("Nat"), Sp, Dot, Sp, Named("mod"), Sp, Parenthesized(Seq(Named("heapColor"), Sp, Parenthesized(Seq(Named("Nat"), Sp, Dot, Sp, Named("div"), Sp, F.Id("v"), Sp, D(2))), Sp, Plus, Sp, Parenthesized(Seq(Named("if"), Sp, Named("Nat"), Sp, Dot, Sp, Named("mod"), Sp, F.Id("v"), Sp, D(2), Sp, Eq, Sp, D(0), Sp, Named("then"), Sp, D(1), Sp, Named("else"), Sp, D(2))))), Sp, D(3)));

    private static Formula Formula1() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("energy"), Sp, F.Id("v"), Sp, Eq, Sp, Named("if"), Sp, F.Id("v"), Sp, Eq, Sp, D(0), Sp, Named("then"), Sp, D(7), Sp, Named("else"), Sp, Named("if"), Sp, Named("heapColor"), Sp, F.Id("v"), Sp, Eq, Sp, D(0), Sp, Named("then"), Sp, D(0), Sp, Named("else"), Sp, Named("if"), Sp, Named("heapColor"), Sp, F.Id("v"), Sp, Eq, Sp, D(1), Sp, Named("then"), Sp, D(1), Sp, Named("else"), Sp, D(3)));

    private static Formula Formula2() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("u"), Sp, F.Id("v"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("heapEdge"), Sp, F.Id("u"), Sp, F.Id("v"), Sp, Iff, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("u"), Sp, Eq, Sp, D(0), Sp, Land, Sp, F.Id("v"), Sp, Eq, Sp, D(1))), Sp, Lor, Sp, Parenthesized(Seq(F.Id("u"), Sp, Eq, Sp, D(1), Sp, Land, Sp, F.Id("v"), Sp, Eq, Sp, D(0))), Sp, Lor, Sp, Parenthesized(Seq(D(2), Sp, Leq, Sp, F.Id("u"), Sp, Land, Sp, Named("Nat"), Sp, Dot, Sp, Named("div"), Sp, F.Id("u"), Sp, D(2), Sp, Eq, Sp, F.Id("v"))), Sp, Lor, Sp, Parenthesized(Seq(D(2), Sp, Leq, Sp, F.Id("v"), Sp, Land, Sp, Named("Nat"), Sp, Dot, Sp, Named("div"), Sp, F.Id("v"), Sp, D(2), Sp, Eq, Sp, F.Id("u")))))));

    private static Formula Formula3() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("meanEnergy"), Sp, F.Id("n"), Sp, Eq, Sp, Parenthesized(Seq(Seq(Sum, Underscore, Grp(Seq(F.Id("v"), Sp, Colon, Sp, Named("Fin"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(2)))))), Sp, Parenthesized(Seq(Named("energy"), Sp, F.Id("v"), Sp, Dot, Sp, Named("val"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))))), Sp, Slash, Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C")))))));

    private static Formula Formula4() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Named("Fin"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(2))))), Sp, Comma, Sp, Named("centeredEnergy"), Sp, F.Id("n"), Sp, F.Id("v"), Sp, Eq, Sp, Parenthesized(Seq(Named("energy"), Sp, F.Id("v"), Sp, Dot, Sp, Named("val"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Minus, Sp, Named("meanEnergy"), Sp, F.Id("n")));

    private static Formula Formula5() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("A"), Sp, F.Id("n"), Sp, Eq, Sp, Named("Matrix"), Sp, Dot, Sp, Named("diagonal"), Sp, Parenthesized(Seq(Named("centeredEnergy"), Sp, F.Id("n")))));

    private static Formula Formula6() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("B"), Sp, F.Id("n"), Sp, Eq, Sp, Parenthesized(Seq(Named("SimpleGraph"), Sp, Dot, Sp, Named("fromRel"), Sp, Parenthesized(Seq(Named("fun"), Sp, Parenthesized(Seq(F.Id("i"), Sp, F.Id("j"), Sp, Colon, Sp, Named("Fin"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(2))))), Sp, Mapsto, Sp, Named("heapEdge"), Sp, F.Id("i"), Sp, Dot, Sp, Named("val"), Sp, F.Id("j"), Sp, Dot, Sp, Named("val"))))), Sp, Dot, Sp, Named("adjMatrix"), Sp, Seq(Mathbb, Grp(F.Id("C")))));

    private static Formula Formula7() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("gen"), Sp, F.Id("n"), Sp, Eq, Sp, Bang, Sp, OpenBracket, Sp, Named("A"), Sp, F.Id("n"), Sp, Comma, Sp, Named("B"), Sp, F.Id("n"), Sp, CloseBracket));

    private static Formula Formula8() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, Named("Fin"), Sp, D(2))), Sp, Comma, Sp, Named("iGen"), Sp, F.Id("n"), Sp, F.Id("i"), Sp, Eq, Sp, Named("HSMul"), Sp, Dot, Sp, Named("hSMul"), Sp, Named("Complex"), Sp, Dot, Sp, Named("I"), Sp, Parenthesized(Seq(Named("gen"), Sp, F.Id("n"), Sp, F.Id("i")))));

    private static Formula Formula9() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("v"), Sp, Colon, Sp, Named("Fin"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(2))))), Sp, Comma, Sp, D(1), Sp, Leq, Sp, F.Id("v"), Sp, Dot, Sp, Named("val"), Sp, To, Sp, Parenthesized(Seq(Named("Matrix"), Sp, Dot, Sp, Named("single"), Sp, F.Id("v"), Sp, D(0), Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, InMacro, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Parenthesized(Seq(Named("gen"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(D(8), Sp, Star, Sp, Named("Nat"), Sp, Dot, Sp, Named("size"), Sp, F.Id("v"), Sp, Dot, Sp, Named("val"))), Sp, Land, Sp, Named("Matrix"), Sp, Dot, Sp, Named("single"), Sp, D(0), Sp, F.Id("v"), Sp, Parenthesized(Seq(D(1), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, InMacro, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Parenthesized(Seq(Named("gen"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(D(8), Sp, Star, Sp, Named("Nat"), Sp, Dot, Sp, Named("size"), Sp, F.Id("v"), Sp, Dot, Sp, Named("val")))))));

    private static Formula Formula10() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("suLieRing"), Sp, F.Id("n"), Sp, Eq, Sp, Named("inferInstanceAs"), Sp, Parenthesized(Seq(Named("LieRing"), Sp, Parenthesized(Seq(Named("suLie"), Sp, F.Id("n")))))));

    private static Formula Formula11() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("suLieAlgebra"), Sp, F.Id("n"), Sp, Eq, Sp, Named("inferInstanceAs"), Sp, Parenthesized(Seq(Named("LieAlgebra"), Sp, Seq(Mathbb, Grp(F.Id("R"))), Sp, Parenthesized(Seq(Named("suLie"), Sp, F.Id("n")))))));

    private static Formula Formula12() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, Named("Fin"), Sp, D(2))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("compactPair"), Sp, F.Id("n"), Sp, F.Id("i"), Sp, Colon, Sp, Named("Matrix"), Sp, Parenthesized(Seq(Named("Fin"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(2))))), Sp, Parenthesized(Seq(Named("Fin"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(2))))), Sp, Seq(Mathbb, Grp(F.Id("C"))))), Sp, Eq, Sp, Named("iGen"), Sp, F.Id("n"), Sp, F.Id("i")));

    private static Formula Formula13() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("I"), Sp, F.Id("K"), Sp, F.Id("M"), Sp, F.Id("N"), Sp, Colon, Sp, Named("Type"), Sp, Star)), Sp, OpenBracket, Sp, Named("CommRing"), Sp, F.Id("K"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieRing"), Sp, F.Id("M"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieAlgebra"), Sp, F.Id("K"), Sp, F.Id("M"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieRing"), Sp, F.Id("N"), Sp, CloseBracket, Sp, OpenBracket, Sp, Named("LieAlgebra"), Sp, F.Id("K"), Sp, F.Id("N"), Sp, CloseBracket, Sp, Parenthesized(Seq(F.Id("f"), Sp, Colon, Sp, Named("LieHom"), Sp, F.Id("K"), Sp, F.Id("M"), Sp, F.Id("N"))), Sp, Parenthesized(Seq(F.Id("S"), Sp, Colon, Sp, F.Id("I"), Sp, To, Sp, F.Id("M"))), Sp, Parenthesized(Seq(F.Id("L"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("Submodule"), Sp, Dot, Sp, Named("map"), Sp, F.Id("f"), Sp, Dot, Sp, Named("toLinearMap"), Sp, Parenthesized(Seq(Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, F.Id("K"))), Sp, F.Id("S"), Sp, F.Id("L"))), Sp, Eq, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, F.Id("K"))), Sp, Parenthesized(Seq(Named("fun"), Sp, Parenthesized(Seq(F.Id("i"), Sp, Colon, Sp, F.Id("I"))), Sp, Mapsto, Sp, F.Id("f"), Sp, Parenthesized(Seq(F.Id("S"), Sp, F.Id("i"))))), Sp, F.Id("L")));

    private static Formula Formula14() => Disp(
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, Named("rightSpan"), Sp, Parenthesized(Seq(F.Id("K"), Sp, Seq(Colon, Eq), Sp, Seq(Mathbb, Grp(F.Id("R"))))), Sp, Parenthesized(Seq(Named("compactPair"), Sp, F.Id("n"))), Sp, Parenthesized(Seq(D(1, 6), Sp, Star, Sp, Parenthesized(Seq(D(1), Sp, Plus, Sp, Named("Nat"), Sp, Dot, Sp, Named("log"), Sp, D(2), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, D(1))))))), Sp, Eq, Sp, Qualified("Top", "top")));
}
