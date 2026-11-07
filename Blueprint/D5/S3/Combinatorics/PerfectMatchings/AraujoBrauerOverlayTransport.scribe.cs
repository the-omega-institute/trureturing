using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class AraujoBrauerOverlayTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constructive results for complete mappings of diagram monoids.",
        H("AraujoBrauerOverlayTransport"),
        Blocks(
            Describe.Lean(DescribeId.Create("araujobraueroverlaytransport-transport-cycle-sign"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.transport_cycle_sign"),
                H("transport_cycle_sign"), StatementSource.FromAuthor(Disp(TransportCycleSignFormula())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The signs of the three labelled transports multiply to the sign of their round trip on A. This identity is consumed by geometric_triangle_sign; the labels are arbitrary equivalences and the statement retains only the Fintype and DecidableEq instances on A."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("araujobrauersignedcycles-halftransportsign"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.halfTransportSign"),
                H("halfTransportSign"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("n"), Sp, F.Id("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Sp, Parenthesized(Seq(F.Id("D"), Sp, F.Id("E"), Sp, Colon, Sp, F.Id("HalfDiagram"), Sp, F.Id("n"), Sp, F.Id("r"))), Sp, Parenthesized(Seq(F.Id("w"), Sp, Colon, Sp, F.Id("OverlayTransport"), Sp, Parenthesized(Seq(F.Id("halfPermutation"), Sp, F.Id("D"))), Sp, Parenthesized(Seq(F.Id("halfPermutation"), Sp, F.Id("E"))))), Sp, Comma, Sp, F.Id("halfTransportSign"), Sp, F.Id("D"), Sp, F.Id("E"), Sp, F.Id("w"), Sp, Eq, Sp, F.Id("Equiv"), Sp, Dot, Sp, F.Id("Perm"), Sp, Dot, Sp, F.Id("sign"), Sp, Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(Parenthesized(Seq(F.Id("Equiv"), Sp, Dot, Sp, F.Id("subtypeEquivRight"), Sp, Parenthesized(Seq(F.Id("halfPermutationFixed"), Sp, F.Id("D"))))), Sp, Dot, Sp, F.Id("trans"), Sp, Parenthesized(Seq(F.Id("D"), Sp, Dot, Sp, D(1), Sp, Dot, Sp, F.Id("val"), Sp, Dot, Sp, F.Id("orderIsoOfFin"), Sp, F.Id("D"), Sp, Dot, Sp, D(1), Sp, Dot, Sp, F.Id("property"))), Sp, Dot, Sp, F.Id("toEquiv"), Sp, Dot, Sp, F.Id("symm"))), Sp, Dot, Sp, F.Id("symm"))), Sp, Dot, Sp, F.Id("trans"), Sp, F.Id("w"), Sp, Dot, Sp, F.Id("transport"))), Sp, Dot, Sp, F.Id("trans"), Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("Equiv"), Sp, Dot, Sp, F.Id("subtypeEquivRight"), Sp, Parenthesized(Seq(F.Id("halfPermutationFixed"), Sp, F.Id("E"))))), Sp, Dot, Sp, F.Id("trans"), Sp, Parenthesized(Seq(F.Id("E"), Sp, Dot, Sp, D(1), Sp, Dot, Sp, F.Id("val"), Sp, Dot, Sp, F.Id("orderIsoOfFin"), Sp, F.Id("E"), Sp, Dot, Sp, D(1), Sp, Dot, Sp, F.Id("property"))), Sp, Dot, Sp, F.Id("toEquiv"), Sp, Dot, Sp, F.Id("symm")))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The formula gives the quantified defining expression."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("araujobrauersignedcycles-signedhalfcycles"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.SignedHalfCycles"),
                H("SignedHalfCycles"), StatementSource.FromAuthor(Disp(Seq(F.Id("structure"), Sp, F.Id("SignedHalfCycles"), Sp, Parenthesized(Seq(F.Id("n"), Sp, F.Id("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, F.Id("where"), Sp, F.Id("cycles"), Sp, Colon, Sp, F.Id("OneTrianglePermutation"), Sp, Parenthesized(Seq(F.Id("HalfDiagram"), Sp, F.Id("n"), Sp, F.Id("r"))), Sp, F.Id("transport"), Sp, Colon, Sp, Forall, Sp, F.Id("D"), Sp, Comma, Sp, F.Id("OverlayTransport"), Sp, Parenthesized(Seq(F.Id("halfPermutation"), Sp, F.Id("D"))), Sp, Parenthesized(Seq(F.Id("halfPermutation"), Sp, Parenthesized(Seq(F.Id("cycles"), Sp, Dot, Sp, F.Id("perm"), Sp, F.Id("D"))))), Sp, F.Id("twoSign"), Sp, Colon, Sp, Forall, Sp, F.Id("D"), Sp, Comma, Sp, F.Id("D"), Sp, Seq(Neg,Sp,InMacro), Sp, F.Id("cycles"), Sp, Dot, Sp, F.Id("triangle"), Sp, To, Sp, F.Id("halfTransportSign"), Sp, F.Id("D"), Sp, Parenthesized(Seq(F.Id("cycles"), Dot, F.Id("perm"), Sp, F.Id("D"))), Sp, Parenthesized(Seq(F.Id("transport"), Sp, F.Id("D"))), Sp, Star, Sp, F.Id("halfTransportSign"), Sp, Parenthesized(Seq(F.Id("cycles"), Sp, Dot, Sp, F.Id("perm"), Sp, F.Id("D"))), Sp, Parenthesized(Seq(F.Id("cycles"), Dot, F.Id("perm"), Sp, Parenthesized(Seq(F.Id("cycles"), Sp, Dot, Sp, F.Id("perm"), Sp, F.Id("D"))))), Sp, Parenthesized(Seq(F.Id("transport"), Sp, Parenthesized(Seq(F.Id("cycles"), Sp, Dot, Sp, F.Id("perm"), Sp, F.Id("D"))))), Sp, Eq, Sp, D(1), Sp, F.Id("threeSign"), Sp, Colon, Sp, Forall, Sp, F.Id("D"), Sp, Comma, Sp, F.Id("D"), Sp, InMacro, Sp, F.Id("cycles"), Sp, Dot, Sp, F.Id("triangle"), Sp, To, Sp, F.Id("halfTransportSign"), Sp, F.Id("D"), Sp, Parenthesized(Seq(F.Id("cycles"), Dot, F.Id("perm"), Sp, F.Id("D"))), Sp, Parenthesized(Seq(F.Id("transport"), Sp, F.Id("D"))), Sp, Star, Sp, F.Id("halfTransportSign"), Sp, Parenthesized(Seq(F.Id("cycles"), Sp, Dot, Sp, F.Id("perm"), Sp, F.Id("D"))), Sp, Parenthesized(Seq(F.Id("cycles"), Dot, F.Id("perm"), Sp, Parenthesized(Seq(F.Id("cycles"), Sp, Dot, Sp, F.Id("perm"), Sp, F.Id("D"))))), Sp, Parenthesized(Seq(F.Id("transport"), Sp, Parenthesized(Seq(F.Id("cycles"), Sp, Dot, Sp, F.Id("perm"), Sp, F.Id("D"))))), Sp, Star, Sp, F.Id("halfTransportSign"), Sp, Parenthesized(Seq(F.Id("cycles"), Sp, Dot, Sp, F.Id("perm"), Sp, Parenthesized(Seq(F.Id("cycles"), Sp, Dot, Sp, F.Id("perm"), Sp, F.Id("D"))))), Sp, Parenthesized(Seq(F.Id("cycles"), Dot, F.Id("perm"), Sp, Parenthesized(Seq(F.Id("cycles"), Sp, Dot, Sp, F.Id("perm"), Sp, Parenthesized(Seq(F.Id("cycles"), Sp, Dot, Sp, F.Id("perm"), Sp, F.Id("D"))))))), Sp, Parenthesized(Seq(F.Id("transport"), Sp, Parenthesized(Seq(F.Id("cycles"), Sp, Dot, Sp, F.Id("perm"), Sp, Parenthesized(Seq(F.Id("cycles"), Sp, Dot, Sp, F.Id("perm"), Sp, F.Id("D"))))))), Sp, Eq, Sp, Minus, Sp, D(1)))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The formula gives the quantified defining expression."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("araujobrauersignedcycles-rank-two-signed-half-cycles"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.rank_two_signed_half_cycles"),
                H("rank_two_signed_half_cycles"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("Nonempty"), Sp, Parenthesized(Seq(F.Id("SignedHalfCycles"), Sp, Parenthesized(Seq(D(6), Sp, Plus, Sp, D(4), Sp, Star, Sp, F.Id("k"))), Sp, D(2)))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The formula gives the quantified statement."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("araujobrauersignedcycles-rank-three-signed-half-cycles"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.rank_three_signed_half_cycles"),
                H("rank_three_signed_half_cycles"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, F.Id("Nonempty"), Sp, Parenthesized(Seq(F.Id("SignedHalfCycles"), Sp, Parenthesized(Seq(D(7), Sp, Plus, Sp, D(4), Sp, Star, Sp, F.Id("k"))), Sp, D(3)))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The formula gives the quantified statement."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("araujobraueroverlaytransport-overlay"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.Overlay"),
                H("Overlay"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("X"), Sp, Colon, Sp, F.Id("Type"), Sp, Star), CloseBrace), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("q"), Sp, Colon, Sp, F.Id("Equiv"), Sp, Dot, Sp, F.Id("Perm"), Sp, F.Id("X"))), Sp, Comma, Sp, F.Id("Overlay"), Sp, F.Id("p"), Sp, F.Id("q"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("Relation"), Sp, Dot, Sp, F.Id("EqvGen"), Sp, Parenthesized(Seq(LambdaLower, Sp, F.Id("u"), Sp, F.Id("v"), Sp, Mapsto, Sp, F.Id("p"), Sp, F.Id("u"), Sp, Eq, Sp, F.Id("v"), Sp, Lor, Sp, F.Id("q"), Sp, F.Id("u"), Sp, Eq, Sp, F.Id("v")))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The formula gives the quantified defining expression."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("araujobraueroverlaytransport-involution-card-mod-two"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.involution_card_mod_two"),
                H("involution_card_mod_two"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("X"), Sp, Colon, Sp, F.Id("Type"), Sp, Star), CloseBrace), Sp, Comma, Sp, Forall, Sp, Seq(OpenBracket, Seq(F.Id("Fintype"), Sp, F.Id("X")), CloseBracket), Sp, Comma, Sp, Forall, Sp, Seq(OpenBracket, Seq(F.Id("DecidableEq"), Sp, F.Id("X")), CloseBracket), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("f"), Sp, Colon, Sp, F.Id("Function"), Sp, Dot, Sp, F.Id("End"), Sp, F.Id("X"))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("Function"), Sp, Dot, Sp, F.Id("Involutive"), Sp, F.Id("f"))), Sp, To, Sp, Parenthesized(Seq(F.Id("Nat"), Sp, Dot, Sp, F.Id("ModEq"), Sp, D(2), Sp, Parenthesized(Seq(F.Id("Nat"), Sp, Dot, Sp, F.Id("card"), Sp, F.Id("X"))), Sp, Parenthesized(Seq(F.Id("Nat"), Sp, Dot, Sp, F.Id("card"), Sp, Parenthesized(Seq(F.Id("Function"), Sp, Dot, Sp, F.Id("fixedPoints"), Sp, F.Id("f")))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The formula gives the quantified statement."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("araujobraueroverlaytransport-overlaytransport"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.OverlayTransport"),
                H("OverlayTransport"), StatementSource.FromAuthor(Disp(Seq(F.Id("structure"), Sp, F.Id("OverlayTransport"), Sp, Seq(OpenBrace, Seq(F.Id("X"), Sp, Colon, Sp, F.Id("Type"), Sp, Star), CloseBrace), Sp, Parenthesized(Seq(F.Id("p"), Sp, F.Id("q"), Sp, Colon, Sp, F.Id("Equiv"), Sp, Dot, Sp, F.Id("Perm"), Sp, F.Id("X"))), Sp, F.Id("where"), Sp, F.Id("transport"), Sp, Colon, Sp, F.Id("Function"), Sp, Dot, Sp, F.Id("fixedPoints"), Sp, F.Id("p"), Sp, Equiv, Sp, F.Id("Function"), Sp, Dot, Sp, F.Id("fixedPoints"), Sp, F.Id("q"), Sp, F.Id("connected"), Sp, Colon, Sp, Forall, Sp, F.Id("x"), Sp, Colon, Sp, F.Id("Function"), Sp, Dot, Sp, F.Id("fixedPoints"), Sp, F.Id("p"), Sp, Comma, Sp, F.Id("Overlay"), Sp, F.Id("p"), Sp, F.Id("q"), Sp, F.Id("x"), Sp, Parenthesized(Seq(F.Id("transport"), Sp, F.Id("x"))), Sp, F.Id("unique"), Sp, Colon, Sp, Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, F.Id("Function"), Sp, Dot, Sp, F.Id("fixedPoints"), Sp, F.Id("p"))), Sp, Parenthesized(Seq(F.Id("y"), Sp, Colon, Sp, F.Id("Function"), Sp, Dot, Sp, F.Id("fixedPoints"), Sp, F.Id("q"))), Sp, Comma, Sp, F.Id("Overlay"), Sp, F.Id("p"), Sp, F.Id("q"), Sp, F.Id("x"), Sp, F.Id("y"), Sp, To, Sp, F.Id("transport"), Sp, F.Id("x"), Sp, Eq, Sp, F.Id("y")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The formula gives the quantified defining expression."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("araujobraueroverlaytransport-halfpermutation"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.halfPermutation"),
                H("halfPermutation"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("n"), Sp, F.Id("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("D"), Sp, Colon, Sp, F.Id("HalfDiagram"), Sp, F.Id("n"), Sp, F.Id("r"))), Sp, Comma, Sp, F.Id("halfPermutation"), Sp, F.Id("D"), Sp, Eq, Sp, Parenthesized(Seq(F.Id("Equiv"), Sp, Dot, Sp, F.Id("Perm"), Sp, Dot, Sp, F.Id("subtypeCongr"), Sp, Parenthesized(Seq(F.Id("Equiv"), Sp, Dot, Sp, F.Id("refl"), Sp, Seq(OpenBrace, Seq(F.Id("x"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"), Sp, Mid, Sp, F.Id("x"), Sp, InMacro, Sp, F.Id("D"), Sp, Dot, Sp, D(1), Sp, Dot, Sp, F.Id("val")), CloseBrace))), Sp, F.Id("D"), Sp, Dot, Sp, D(2), Sp, Dot, Sp, F.Id("val")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The formula gives the quantified defining expression."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("araujobraueroverlaytransport-halfpermutationfixed"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.halfPermutationFixed"),
                H("halfPermutationFixed"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("n"), Sp, F.Id("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("D"), Sp, Colon, Sp, F.Id("HalfDiagram"), Sp, F.Id("n"), Sp, F.Id("r"))), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, F.Id("Fin"), Sp, F.Id("n"))), Sp, Comma, Sp, F.Id("halfPermutation"), Sp, F.Id("D"), Sp, F.Id("x"), Sp, Eq, Sp, F.Id("x"), Sp, Iff, Sp, F.Id("x"), Sp, InMacro, Sp, F.Id("D"), Sp, Dot, Sp, D(1), Sp, Dot, Sp, F.Id("val")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The formula gives the quantified statement."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("araujobraueroverlaytransport-halfpermutationinvolutive"), DeclarationHandle.Create("D5/S3/Combinatorics/PerfectMatchings/AraujoBrauerOverlayTransport.halfPermutationInvolutive"),
                H("halfPermutationInvolutive"), StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("n"), Sp, F.Id("r"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Sp, Comma, Sp, Forall, Sp, Parenthesized(Seq(F.Id("D"), Sp, Colon, Sp, F.Id("HalfDiagram"), Sp, F.Id("n"), Sp, F.Id("r"))), Sp, Comma, Sp, F.Id("Function"), Sp, Dot, Sp, F.Id("Involutive"), Sp, Parenthesized(Seq(F.Id("halfPermutation"), Sp, F.Id("D")))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The formula gives the quantified statement."))), DescribeRole.Theorem))));

    private static Formula TransportCycleSignFormula()
    {
        var a = F.Id("A");
        var b = F.Id("B");
        var c = F.Id("C");
        var r = F.Id("r");
        var fin = Seq(F.Id("Fin"), Sp, r);
        var eZero = Seq(F.Id("e"), Underscore, Grp(D(0)));
        var eOne = Seq(F.Id("e"), Underscore, Grp(D(1)));
        var eTwo = Seq(F.Id("e"), Underscore, Grp(D(2)));
        var tZeroOne = Seq(F.Id("t"), Underscore, Grp(D(0, 1)));
        var tOneTwo = Seq(F.Id("t"), Underscore, Grp(D(1, 2)));
        var tTwoZero = Seq(F.Id("t"), Underscore, Grp(D(2, 0)));
        return Seq(
            Forall, Sp, Seq(OpenBrace, a, Sp, b, Sp, c, Sp, Colon, Sp, F.Id("Type"), Star, CloseBrace), Sp, Comma, Sp,
            Forall, Sp, Seq(OpenBracket, F.Id("Fintype"), Sp, a, CloseBracket), Sp, Comma, Sp,
            Forall, Sp, Seq(OpenBracket, F.Id("DecidableEq"), Sp, a, CloseBracket), Sp, Comma, Sp,
            Forall, Sp, Seq(OpenBrace, r, Sp, Colon, Sp, Mathbb, Grp(F.Id("N")), CloseBrace), Sp, Comma, Sp,
            Forall, Sp, Bound(eZero, Seq(a, Sp, Equiv, Sp, fin)), Sp,
            Bound(eOne, Seq(b, Sp, Equiv, Sp, fin)), Sp,
            Bound(eTwo, Seq(c, Sp, Equiv, Sp, fin)), Sp,
            Bound(tZeroOne, Seq(a, Sp, Equiv, Sp, b)), Sp,
            Bound(tOneTwo, Seq(b, Sp, Equiv, Sp, c)), Sp,
            Bound(tTwoZero, Seq(c, Sp, Equiv, Sp, a)), Sp, Comma, Sp,
            Sign(Trans(Trans(Symm(eZero), tZeroOne), eOne)), Sp, Star, Sp,
            Sign(Trans(Trans(Symm(eOne), tOneTwo), eTwo)), Sp, Star, Sp,
            Sign(Trans(Trans(Symm(eTwo), tTwoZero), eZero)), Sp, Eq, Sp,
            Sign(Trans(Trans(tZeroOne, tOneTwo), tTwoZero)));
    }

    private static Formula Bound(Formula name, Formula type) =>
        Parenthesized(Seq(name, Sp, Colon, Sp, type));

    private static Formula Symm(Formula value) => Seq(value, Dot, F.Id("symm"));

    private static Formula Trans(Formula first, Formula second) =>
        Parenthesized(Seq(first, Dot, F.Id("trans"), Sp, second));

    private static Formula Sign(Formula value) =>
        Seq(F.Id("Equiv"), Dot, F.Id("Perm"), Dot, F.Id("sign"), Sp, value);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
