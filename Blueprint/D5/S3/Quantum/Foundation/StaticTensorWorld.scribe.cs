using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class StaticTensorWorldDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Foundation/StaticTensorWorld.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A closed world of all finite real tensor words has positive Frobenius comparisons, every actual module and conditional-action identity, zero generators at every label, and a nonassociative symmetric-matrix local object.",
        H("A closed static world with nonassociative local comparison"), Blocks(
            Paragraph(Text("The local space is the entire real symmetric two by two matrix space, with symmetrized matrix multiplication and the trace pairing. Every finite parenthesized tensor word, including the empty word, is supplied. Every ordered pair of words has an actual edge whose output is the same object later reused in the family. No active object or quantum representation is assumed.")),
            Def("comparison", "Comparison", "Finite positive comparison objects", ComparisonFormula(),
                "Comparison bundles a nontrivial finite-dimensional real inner product space E, a unit e, a real bilinear operation S, and a real linear label assignment D into real linear endomorphisms. S is commutative, S(e,x)=x, the inner product satisfies the Frobenius identity, and D(h) is a derivation of this same S for every h. The inner product structure supplies symmetry, bilinearity and strict positivity on every nonzero vector. No Jordan, associative, alternating or Lie identity is included."),
            Def("static", "IsStatic", "Zero assignment at every label", All("A", C("Comparison"),
                Iff(C("IsStatic", V("A")), Equal(C("action", V("A")), D(0)))),
                "An object is static exactly when its entire linear map into endomorphisms is zero. This quantifies every label and every vector. It is stronger than setting one chosen Hamiltonian to zero."),
            Def("actual-edge", "ActualEdge", "The full actual binary contract", EdgeFormula(),
                "For A,B,C, an actual edge carries a real linear equivalence from the entire carrier of C onto the algebraic tensor product of the carriers of A and B. It identifies the unit and the product pairing on simple tensors. Both module identities and both value-preserving conditional-action identities hold for all displayed arguments. C is the actual output Comparison, so its same multiplication, inner product and complete derivation law are retained on reuse. Product pairings are a permitted particular case of the arbitrary positive Frobenius pairing allowed by the source contract."),
            Def("tensor", "tensor", "Actual pure tensor comparison", TensorFormula(),
                "For arbitrary positive Comparison objects A and B, tensor A B has the full real algebraic tensor carrier, the tensor unit, the bilinear tensor product of the two comparisons, the standard positive tensor inner product, and zero label assignment. The tensor comparison is commutative, unital and Frobenius for all joint vectors, including sums of simple tensors. Tensor inner-product positivity is the upstream positive tensor construction; it is not a premise asserting positivity of an invented family. When A and B are static, the identity carrier equivalence proves all actual-edge identities."),
            Def("symmetric-domain", "SymTwo", "The actual local domain", Equal(C("SymTwo"),
                C("HermitianMat", C("Fin", D(2)), C("Real"))),
                "HermitianMat over the real field is precisely the full symmetric matrix subspace: real conjugation is trivial, so the adjoint is transpose. It has all real entries allowed by symmetry, with no discrete or rational restriction. The imported HermitianMat inner product is the actual trace of the matrix product, and the finite-dimensional and positive-definite structures are reused."),
            Def("symmetric-product", "symMul", "Symmetrized matrix comparison", SymFormula(),
                "The multiplication is the self-adjoint part of ordinary matrix multiplication. On symmetric real inputs its matrix is exactly one half of ac+ca. Trace cyclicity proves the Frobenius identity; symmetry and the matrix identity give commutativity and the unit law."),
            Def("local-object", "localObject", "The symmetric-matrix comparison with zero assignment", Equal(C("localObject"),
                C("ComparisonData", C("SymTwo"), C("symMul"), C("TracePairing"), C("Identity"), D(0))),
                "The local carrier is SymTwo, the comparison is symMul, the unit is the identity matrix, the pairing is Tr(ac), and D is identically zero. Each of these is actual constructed data. Every label endomorphism is a derivation because both sides of the derivation identity vanish."),
            Def("scalar-object", "scalarObject", "The empty-word scalar comparison", Equal(C("scalarObject"),
                C("ComparisonData", C("Real"), C("RealMultiplication"), C("RealPairing"), D(1), D(0))),
                "The empty word has carrier R, ordinary multiplication and inner product, unit one, and zero assignment. It is finite and nontrivial."),
            Def("word", "Word", "All finite tensor words", Equal(C("Word"), C("FreeBinaryWords", C("empty"), C("local"))),
                "Word has constructors empty, local and pair(u,v), with arbitrary recursively generated finite u and v. There is no maximum length, finite-depth cap or restriction to a fixed parenthesization. Empty represents the real tensor unit; local represents the symmetric matrix object."),
            Def("objects", "object", "One unchanged object for each word", Seq(
                Equal(C("object", C("empty")), C("scalarObject")), Comma, Sp,
                Equal(C("object", C("local")), C("localObject")), Comma, Sp,
                All("u", C("Word"), All("v", C("Word"), Equal(C("object", C("pair", V("u"), V("v"))),
                    C("tensor", C("object", V("u")), C("object", V("v"))))))),
                "The recursion defines an actual object at each finite word. At a pair, its carrier is definitionally the full real tensor product of the two previous carriers. Its comparison and inner product are the pure tensors of those same previous data. The same recursion is applied at every depth."),
            Def("world", "StaticWorld", "Closed all-static actual worlds", WorldFormula(),
                "A StaticWorld provides a Comparison at every word, proves that all their label assignments are zero, and supplies an ActualEdge for every ordered pair into that world's same pair word. The object contract includes finite dimension, nonzero real carrier, positive Frobenius comparison and the full derivation law. The edge contract includes the complete module and conditional-action laws, rather than just unit-embedding equalities."),
            Def("counterworld", "counterworld", "The constructed all-finite static world", Equal(C("counterworld"), C("StaticWorldData", C("object"))),
                "This world uses the actual recursive object family. Each edge uses the identity equivalence on the real tensor carrier. For simple inputs its comparison is S_A(a,c) tensor S_B(b,d); the two module identities follow from the units. Both conditional actions are zero at every label, and the complete joint derivation law is zero equals zero plus zero for arbitrary joint vectors. All intermediate outputs remain in this same family and retain their same data. Every member is static, so no member can be an active partner for any other member."),
            Def("claim", "claim", "The consequence that fails without active partners", ClaimFormula(),
                "The claim says every comparison in every closed all-static actual world is associative. This is the static classical conclusion that the activity hypothesis would enforce; it is not a claim that a particular Hamiltonian must be nonzero. Refuting it requires the complete constructed world, not only a matrix identity detached from its joint contracts."),
            Def("pauli-z", "pauliZ", "A real diagonal Pauli matrix", Equal(C("pauliZ"), C("Diagonal", D(1), Seq(Minus, D(1)))),
                "pauliZ is diag(1,-1), as an element of the actual symmetric matrix space."),
            Def("pauli-x", "pauliX", "A real off-diagonal Pauli matrix", Equal(C("pauliX"), C("MatrixRows", D(0), D(1), D(1), D(0))),
                "pauliX has rows (0,1) and (1,0). In the actual local comparison, S(Z,X)=0 and S(X,X)=I. Hence S(S(Z,X),X)=0, while S(Z,S(X,X))=Z is nonzero. Equivalently the local left-multiplication commutator [L_Z,L_X]X is Z."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("Full static tensor closure does not force associativity"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, C("claim")))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the claimed universal associativity to counterworld, its local word and the actual matrices Z,X,X. The two nested products have unequal top-left entries, contradicting that claim. The counterworld already supplies all finite real domains, positive pairings and actual edges, and every generator at every label vanishes. Thus removing active partners leaves a complete static world with nonassociative local comparison. Nonassociativity also prevents this static local object from being a finite real direct-product classical algebra. This conclusion does not assert that the symmetric local comparison fails the Jordan identity, nor does it identify zero label assignment with the zero-Hamiltonian case of an otherwise active complex quantum object."))), DescribeRole.Theorem))));

    private static DocumentBlock Def(string id, string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args)
    {
        var parts = new List<Formula> { Operatorname, Grp(F.Id(name)) };
        if (args.Length != 0)
        {
            parts.Add(Open);
            for (var i = 0; i < args.Length; ++i)
            {
                if (i != 0) parts.AddRange([Comma, Sp]);
                parts.Add(args[i]);
            }
            parts.Add(Close);
        }
        return Seq([.. parts]);
    }
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Typed(Formula x, Formula t) => Parenthesized(Seq(x, Colon, Sp, t));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, body);
    private static Formula Conj(params Formula[] xs)
    {
        var parts = new List<Formula>();
        for (var i = 0; i < xs.Length; ++i)
        {
            if (i != 0) parts.AddRange([Sp, Land, Sp]);
            parts.Add(Parenthesized(xs[i]));
        }
        return Seq([.. parts]);
    }
    private static Formula Iff(Formula a, Formula b) => Seq(a, Sp, IffToken(), Sp, b);
    private static Formula IffToken() => FormulaDsl.Iff;
    private static Formula E(Formula a) => C("Carrier", a);
    private static Formula U(Formula a) => C("unit", a);
    private static Formula S(Formula a, Formula x, Formula y) => C("mul", a, x, y);
    private static Formula Act(Formula a, Formula h, Formula x) => C("action", a, h, x);
    private static Formula G(Formula a, Formula x, Formula y) => C("InnerProduct", a, x, y);
    private static Formula T(Formula a, Formula b) => C("Tensor", a, b);
    private static Formula Out(Formula edge, Formula x) => C("carrier", edge, x);
    private static Formula In(Formula edge, Formula x) => C("inverseCarrier", edge, x);
    private static Formula ComparisonFormula()
    {
        var a = V("A"); var x = V("x"); var y = V("y"); var z = V("z"); var h = V("h");
        var comm = All("x", E(a), All("y", E(a), Equal(S(a,x,y), S(a,y,x))));
        var unit = All("x", E(a), Equal(S(a,U(a),x),x));
        var frobenius = All("x", E(a), All("y", E(a), All("z", E(a),
            Equal(G(a,S(a,x,y),z), G(a,y,S(a,x,z))))));
        var derivation = All("h", E(a), All("x", E(a), All("y", E(a),
            Equal(Act(a,h,S(a,x,y)), Add(S(a,Act(a,h,x),y), S(a,x,Act(a,h,y)))))));
        return All("A", C("Comparison"), Conj(
            C("NontrivialFiniteRealInnerProductSpace", E(a)),
            C("RealBilinear", C("mul", a)), C("RealLinear", C("action", a)),
            comm, unit, frobenius, derivation));
    }
    private static Formula EdgeFormula()
    {
        var a=V("A"); var b=V("B"); var c=V("C"); var e=V("e");
        var x=V("x"); var y=V("y"); var z=V("z"); var t=V("t");
        var carrier = C("RealLinearEquivalence", C("carrier",e), E(c), C("RealTensorProduct",E(a),E(b)));
        var unit = Equal(Out(e,U(c)), T(U(a),U(b)));
        var pairing = All("x",E(a),All("y",E(b),All("z",E(a),All("t",E(b),
            Equal(G(c,In(e,T(x,y)),In(e,T(z,t))),Multiply(G(a,x,z),G(b,y,t)))))));
        var leftModule = All("x",E(a),All("z",E(a),All("t",E(b),
            Equal(Out(e,S(c,In(e,T(x,U(b))),In(e,T(z,t)))),T(S(a,x,z),t)))));
        var rightModule = All("y",E(b),All("z",E(a),All("t",E(b),
            Equal(Out(e,S(c,In(e,T(U(a),y)),In(e,T(z,t)))),T(z,S(b,y,t))))));
        var leftConditional = All("x",E(a),All("y",E(b),All("z",E(a),
            Equal(Out(e,Act(c,In(e,T(x,y)),In(e,T(z,U(b))))),T(Act(a,x,z),y)))));
        var rightConditional = All("x",E(a),All("y",E(b),All("t",E(b),
            Equal(Out(e,Act(c,In(e,T(x,y)),In(e,T(U(a),t)))),T(x,Act(b,y,t))))));
        return All("A", C("Comparison"), All("B", C("Comparison"), All("C", C("Comparison"),
            All("e", C("ActualEdge",a,b,c), Conj(carrier,unit,pairing,leftModule,rightModule,
                leftConditional,rightConditional)))));
    }
    private static Formula TensorFormula() => All("A", C("Comparison"), All("B", C("Comparison"),
        Equal(C("tensor", V("A"), V("B")), C("ComparisonData", C("RealTensorCarrier", V("A"), V("B")),
            C("BilinearTensor", C("mul", V("A")), C("mul", V("B"))), C("ProductInner", V("A"), V("B")),
            C("TensorUnit", V("A"), V("B")), D(0)))));
    private static Formula SymFormula() => All("a", C("SymTwo"), All("b", C("SymTwo"),
        Equal(C("mat", C("symMul", V("a"), V("b"))), Seq(new Formula.Fraction(D(1), D(2)), Sp,
            Parenthesized(Seq(C("mat", V("a")), C("mat", V("b")), Sp, Plus, Sp,
                C("mat", V("b")), C("mat", V("a"))))))));
    private static Formula WorldFormula() => All("W", C("StaticWorld"), Conj(
        All("w", C("Word"), C("IsStatic", C("field", V("W"), V("w")))),
        All("u", C("Word"), All("v", C("Word"), C("ActualEdge", C("field", V("W"), V("u")),
            C("field", V("W"), V("v")), C("field", V("W"), C("pair", V("u"), V("v"))))))));
    private static Formula ClaimFormula() => Equal(C("claim"), All("W", C("StaticWorld"), All("w", C("Word"),
        All("a", C("Carrier", C("field", V("W"), V("w"))),
        All("b", C("Carrier", C("field", V("W"), V("w"))),
        All("c", C("Carrier", C("field", V("W"), V("w"))),
            Equal(C("mul", C("field", V("W"), V("w")),
                C("mul", C("field", V("W"), V("w")), V("a"), V("b")), V("c")),
                C("mul", C("field", V("W"), V("w")), V("a"),
                    C("mul", C("field", V("W"), V("w")), V("b"), V("c"))))))))));
}
