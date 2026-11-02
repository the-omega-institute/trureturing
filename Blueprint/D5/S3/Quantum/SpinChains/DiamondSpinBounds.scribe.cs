using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class DiamondSpinBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/DiamondSpinBounds.";
    private static readonly Formula S = F.Id("S");
    private static readonly Formula I = F.Id("i");
    private static readonly Formula J = F.Id("j");
    private static readonly Formula V = F.Id("v");
    private static readonly Formula X = F.Id("x");
    private static readonly Formula Y = F.Id("y");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native normalized spin operators on four complete complex factors satisfy weight invariance, singlet isotropy and a uniform pair-order bound.",
        H("Native operators and bounds for the equal-spin diamond"), Blocks(
            Paragraph(Text("Let S be a natural number. Each of the four factors is the complete complex spin-S space with orthonormal basis indexed by W(S) = Fin(2S+1). Index r has weight S−r; the native normalized raising matrix Jplus(2S) has coefficient √((r+1)(2S−r)) from r+1 to r, with zero endpoint, and lowering is its adjoint. Put C(S) = Fin(4) → W(S), V(S) = C(S) → ℂ and O(S) = Matrix(C(S),C(S),ℂ). Norms are the Euclidean norms and inner products conjugate the first argument. Matrices act on every complex superposition in V(S). Sites 0,1,2,3 correspond to vertices 1,2,3,4. A submodule infimum denotes intersection; bottom is the zero submodule.")),
            Node("site", "An operator at one site", "site",
                Spin(All(I, Call("Fin", D(4)), All(F.Id("A"), Call("Matrix", W(), W(), Complexes()),
                    All(X, C(), All(Y, C(), Equal(Call("site", S, I, F.Id("A"), X, Y),
                        Mul(Call("A", At(X, I), At(Y, I)), Call("prodExcept", I, X, Y)))))))),
                "prodExcept(i,x,y) is the product of Kronecker deltas δ(xⱼ,yⱼ) over the three sites j≠i. Thus site is exactly the tensor placement of A with identities on all other factors."),
            Node("raising", "The raising operator at a site", "raising",
                Spin(All(I, Call("Fin", D(4)), Equal(Call("raising", S, I), Call("site", S, I, Call("Jplus", Mul(D(2), S)))))),
                "This is the normalized native raising matrix on the full factor."),
            Node("lowering", "The lowering operator at a site", "lowering",
                Spin(All(I, Call("Fin", D(4)), Equal(Call("lowering", S, I), Call("site", S, I, Adj(Call("Jplus", Mul(D(2), S))))))),
                "The adjoint convention includes both ladder endpoints."),
            Node("edges", "The five edges", "edges",
                Equal(Call("edges"), Call("finset", Pair(0,1), Pair(0,2), Pair(0,3), Pair(1,2), Pair(1,3))),
                "Each listed unordered edge is included once. The absent edge is (2,3); there are no loops or additional coefficients."),
            Node("hamiltonian", "The diamond Hamiltonian", "hamiltonian", HamiltonianFormula(),
                "Writing Xᵢ=site(S,i,Jx(2S)) and Yᵢ=site(S,i,Jy(2S)), this is 2Σedges(XᵢXⱼ+YᵢYⱼ). The native Cartesian identity proves it equals Σedges(Jᵢ⁺Jⱼ⁻+Jᵢ⁻Jⱼ⁺), with coefficient +1 on each of the five edges. Operators at distinct sites commute, so the Hamiltonian is Hermitian."),
            Node("total-raising", "Total raising", "totalRaising",
                Spin(Equal(Call("totalRaising", S), SumSites(Call("raising", S, I)))),
                "The sum runs over all four sites."),
            Node("total-lowering", "Total lowering", "totalLowering",
                Spin(Equal(Call("totalLowering", S), SumSites(Call("lowering", S, I)))),
                "This is the adjoint of total raising."),
            Node("total-weight", "Total weight", "totalWeight",
                Spin(Equal(Call("totalWeight", S), SumSites(Call("site", S, I, Call("Jz", Mul(D(2), S)))))),
                "At configuration x its diagonal entry is 4S−Σᵢxᵢ. The Hamiltonian commutes with total weight."),
            Node("singlets", "The entire singlet space", "singletSpace",
                Spin(Equal(Call("singletSpace", S), Call("inf", Call("ker", Call("totalRaising", S)), Call("ker", Call("totalLowering", S))))),
                "Both kernels are taken on V(S). No pair-coupling sector or multiplicity is selected. The total ladder commutator implies that every vector here has total weight zero."),
            Node("zero-weight", "The entire zero-weight space", "zeroWeightSpace",
                Spin(Equal(Call("zeroWeightSpace", S), Call("ker", Call("totalWeight", S)))),
                "It consists exactly of vectors supported on configurations Z(S) with Σᵢxᵢ=4S. These coordinate vectors form an orthonormal basis of the entire kernel. The middle configuration xᵢ=S belongs to Z(S), including at S=0."),
            Node("restriction", "The actual Hermitian restriction", "restrictedHamiltonian",
                Spin(All(X, Call("Z", S), All(Y, Call("Z", S), Equal(Call("restrictedHamiltonian", S, X, Y), Call("hamiltonian", S, Call("val", X), Call("val", Y)))))),
                "Z(S) is the subtype of C(S) just described. Invariance of zero weight identifies this submatrix with the genuine restricted operator, including its action, inner product and eigenvectors."),
            Node("z", "The weight operator at a site", "z",
                Spin(All(I, Call("Fin", D(4)), Equal(Call("z", S, I), Call("site", S, I, Call("Jz", Mul(D(2), S)))))),
                "At configuration x the diagonal entry is S−xᵢ."),
            Node("xy", "The transverse pair operator", "xy",
                Spin(All(I, Call("Fin", D(4)), All(J, Call("Fin", D(4)), Equal(Call("xy", S, I, J), Add(Mul(Call("raising", S, I), Call("lowering", S, J)), Mul(Call("lowering", S, I), Call("raising", S, J))))))),
                "Both ladder products act on the complete four-factor carrier."),
            Node("zz", "The vertical pair operator", "zz",
                Spin(All(I, Call("Fin", D(4)), All(J, Call("Fin", D(4)), Equal(Call("zz", S, I, J), Mul(Call("z", S, I), Call("z", S, J)))))),
                "For distinct sites this is their commuting weight product."),
            Node("dot", "The isotropic pair operator", "dot",
                Spin(All(I, Call("Fin", D(4)), All(J, Call("Fin", D(4)), Equal(Call("dot", S, I, J), Add(Mul(new Formula.Fraction(D(1), D(2)), Call("xy", S, I, J)), Call("zz", S, I, J))))))),
                "This is XᵢXⱼ+YᵢYⱼ+ZᵢZⱼ. The native pair bound holds for every distinct pair."),
            Node("isotropic", "The isotropic diamond sum", "isotropic",
                Spin(Equal(Call("isotropic", S), Seq(new Formula.Subscript(Sum, Seq(PairVariables(), InMacro, Call("edges"))), Sp, Call("dot", S, I, J)))),
                "All five coefficient-one edges are present."),
            Node("vertical", "The vertical diamond sum", "vertical",
                Spin(Equal(Call("vertical", S), Seq(new Formula.Subscript(Sum, Seq(PairVariables(), InMacro, Call("edges"))), Sp, Call("zz", S, I, J)))),
                "This is the diagonal sum over exactly the same five edges."),
            Node("expect", "The homogeneous complex quadratic form", "expect",
                Spin(All(V, Call("V", S), All(F.Id("A"), Call("O", S), Equal(Call("expect", V, F.Id("A")), Call("inner", V, Mul(F.Id("A"), V)))))) ,
                "The inner product conjugates v in its first argument. No normalization is assumed."),
            Node("middle", "The middle configuration", "middleConfiguration",
                Spin(All(I, Call("Fin", D(4)), Equal(Call("middleConfiguration", S, I), S))),
                "Every coordinate is the basis index S, of local weight zero."),
            Node("binomial", "The positive binomial product", "binomialProduct",
                Spin(All(X, C(), Equal(Call("binomialProduct", S, X), Call("ofReal", Call("binomialProductReal", S, X))))),
                "It is the tensor product of the native binomial vectors at real parameter one."),
            Node("binomial-real", "Its real coefficients", "binomialProductReal",
                Spin(All(X, C(), Equal(Call("binomialProductReal", S, X), Seq(new Formula.Subscript(Prod, Seq(I, InMacro, Call("Fin", D(4)))), Sp, Call("sqrt", Call("choose", Mul(D(2), S), Call("val", At(X, I)))))))),
                "Every coefficient is strictly positive, including at both endpoints."),
            Describe.Lean(DescribeId.Create("diamond-native-relations"), DeclarationHandle.Create(Prefix + "native_relations"),
                H("Native spin relations and the whole-carrier pair bound"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The conjunction records the exact site action, linearity, adjoints and commutation, the normalized ladder products, weight support and invariance, Hermiticity of the restriction, singlet expectation isotropy, and the pair order bound. Every spin, site, matrix and vector variable retains its full stated range.")),
                    Paragraph(Text("A strictly positive product of binomial vectors is a Dᵢⱼ eigenvector of eigenvalue S². Adding S² times the identity to Dᵢⱼ gives an entrywise nonnegative matrix. The Perron comparison bound and the Hermitian spectral theorem yield Dᵢⱼ≤S²I for S≥1 on the whole complex carrier, with every coupling sector and multiplicity included.")),
                    Paragraph(Text("Total-ladder commutators give ⟨v,Kv⟩=(4/3)⟨v,Iv⟩ for every singlet. This is an expectation identity; no vector equation Kv=(4/3)Iv is asserted. Both total ladders imply zero total weight, and weight invariance identifies the displayed submatrix with the complete Hermitian restriction."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("diamond-spin-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula All(Formula x, Formula type, Formula body) => Seq(Forall,Sp,P(Seq(x,Colon,Sp,type)),Comma,Sp,P(body));
    private static Formula Spin(Formula body) => All(S,Nat(),body);
    private static Formula W() => Call("W",S);
    private static Formula C() => Call("C",S);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula LE(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula LT(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThan,y);
    private static Formula Mem(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.MemberOf,y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Add,y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Subtract,y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Multiply,y);
    private static Formula Pow(Formula x, byte n) => new Formula.Power(x,D(n));
    private static Formula Adj(Formula x) => new Formula.Power(P(x),Star);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(P(x),FormulaLogicOperator.And,P(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(P(x),FormulaLogicOperator.Implies,P(y));
    private static Formula SumSites(Formula x) => Seq(new Formula.Subscript(Sum,Seq(I,InMacro,Call("Fin",D(4)))),Sp,x);
    private static Formula Pair(byte a, byte b) => Seq(Open,D(a),Comma,D(b),Close);
    private static Formula HamiltonianFormula() => Spin(Equal(Call("hamiltonian",S),
        Seq(new Formula.Subscript(Sum,Seq(PairVariables(),InMacro,Call("edges"))),Sp,
            Mul(D(2),P(Add(Mul(Call("X",I),Call("X",J)),Mul(Call("Y",I),Call("Y",J))))))));
    private static Formula GroundSpaceFormula()
    {
        var shifted = Sub(Call("hamiltonian", S),
            Mul(Call("ofReal", Call("groundEnergy", S)), D(1)));
        return Spin(Equal(Call("groundSpace", S),
            Call("inf", Call("ker", shifted), Call("zeroWeightSpace", S))));
    }
    private static Formula PairVariables() => Seq(Open,I,Comma,J,Close);
    private static Formula ClaimFormula() => new Formula.Logic(Call("claim"),FormulaLogicOperator.Iff,
        Spin(Imp(LE(D(1),S), And(
            All(V,Call("V",S),Imp(And(Mem(V,Call("singletSpace",S)),Equal(Call("norm",V),D(1))),
                LE(Call("singletLowerBound",S),Call("re",Call("inner",V,Mul(Call("hamiltonian",S),V)))))),
            And(LT(Call("groundEnergy",S),Call("singletLowerBound",S)),
                Equal(Call("inf",Call("groundSpace",S),Call("singletSpace",S)),Call("bottom")))))));
}
