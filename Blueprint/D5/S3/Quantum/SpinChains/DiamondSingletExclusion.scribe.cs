using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class DiamondSingletExclusionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/DiamondSingletExclusion.";
    private static readonly Formula S = F.Id("S");
    private static readonly Formula V = F.Id("v");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive integer spin, the coefficient-one diamond has no singlet ground vector in its entire zero-weight sector.",
        H("Singlet exclusion for the equal-spin diamond"), Blocks(
            Paragraph(Text("Let S be a natural number. Each of the four factors is the complete complex spin-S space with orthonormal basis indexed by W(S) = Fin(2S+1). Index r has weight S−r; the native normalized raising matrix Jplus(2S) has coefficient √((r+1)(2S−r)) from r+1 to r, with zero endpoint, and lowering is its adjoint. Put C(S) = Fin(4) → W(S), V(S) = C(S) → ℂ and O(S) = Matrix(C(S),C(S),ℂ). Norms are the Euclidean norms and inner products conjugate the first argument. Matrices act on every complex superposition in V(S). Sites 0,1,2,3 correspond to vertices 1,2,3,4. A submodule infimum denotes intersection; bottom is the zero submodule.")),
            Node("minimum", "The ground energy", "groundEnergy",
                Spin(Equal(Call("groundEnergy", S), Call("sInf", Call("spectrumReal", Call("restrictedHamiltonian", S))))),
                "The restricted Hermitian matrix has finite nonempty real spectrum. Its infimum belongs to that spectrum and is its least element, so groundEnergy is the actual attained minimum."),
            Node("ground-space", "The entire zero-weight ground eigenspace", "groundSpace",
                GroundSpaceFormula(),
                "The identity matrix in this expression acts on V(S). Intersecting its kernel with zero weight includes every vector of the minimum eigenspace and all degeneracies."),
            Node("bound", "The singlet threshold", "singletLowerBound",
                Spin(Equal(Call("singletLowerBound", S), Sub(new Formula.Negate(Mul(D(4), Pow(S,2))), Mul(new Formula.Fraction(D(8),D(3)),S)))),
                "The threshold L(S)=−4S²−8S/3 is strictly negative for every S≥1."),
            Node("claim", "All three conclusions", "claim", ClaimFormula(),
                "All clauses hold for every integer spin S≥1. The first clause covers every unit complex singlet; the second compares the entire zero-weight minimum with the threshold; the third excludes all nonzero singlet ground vectors."),
            Describe.Lean(DescribeId.Create("diamond-singlet-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Uniform bound, strict comparison and singlet exclusion"),
                StatementSource.FromAuthor(Disp(Call("claim"))), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let Dᵢⱼ = (Jᵢ⁺Jⱼ⁻+Jᵢ⁻Jⱼ⁺)/2 + ZᵢZⱼ and I = Σedges Dᵢⱼ. A strictly positive product of binomial vectors is a Dᵢⱼ eigenvector with eigenvalue S². Adding S² times the identity to Dᵢⱼ gives an entrywise nonnegative matrix. The Perron comparison bound and the Hermitian spectral theorem yield Dᵢⱼ≤S²I on the whole complex carrier. This includes every coupling sector.")),
                    Paragraph(Text("For any singlet v, total-ladder commutators give the expectation identity ⟨v,Kv⟩=(4/3)⟨v,Iv⟩. This is an expectation identity, not the vector equation Kv=(4/3)Iv. The central-pair Casimir expansion gives Iv=−2S(S+1)v−D₀₁v. Applying the full-carrier pair bound proves the singlet threshold for every unit v.")),
                    Paragraph(Text("For strict comparison, define an unnormalized vector t supported on Σᵢrᵢ=4S by t(r)=(-1)^p Πᵢ√C(2S,rᵢ)/C(4S,p), where p=r₀+r₁. Adjacent binomial recurrences prove that both total ladders annihilate t, including all endpoint cases. Its middle coefficient is nonzero and D₀₁t=S²t. Hence ⟨t,Kt⟩=L(S)⟨t,t⟩.")),
                    Paragraph(Text("Put Tz=Σedges ZᵢZⱼ. The exact double commutator [Jtotal⁺,[Jtotal⁻,K]]=2K−8Tz forces Tz v=(e/4)v for every singlet K-eigenvector of eigenvalue e. At the middle configuration Tz has diagonal entry zero. Since t has a nonzero coefficient there and L(S)<0, t cannot be a K-eigenvector of eigenvalue L(S).")),
                    Paragraph(Text("If the restricted minimum were at least L(S), the Hermitian matrix Krestricted−L(S)I would be positive semidefinite. The zero quadratic form of the restricted t would place it in that matrix's kernel, contradicting the preceding non-eigenvector result. Thus the actual minimum is strictly below L(S). Finally any nonzero ground singlet could be normalized and would contradict the unit-singlet lower bound. The full ground-singlet intersection is therefore zero."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("diamond-singlet-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula All(Formula x, Formula type, Formula body) => Seq(Forall,Sp,P(Seq(x,Colon,Sp,type)),Comma,Sp,P(body));
    private static Formula Spin(Formula body) => All(S,Nat(),body);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula LE(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula LT(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.LessThan,y);
    private static Formula Mem(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.MemberOf,y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Subtract,y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Multiply,y);
    private static Formula Pow(Formula x, byte n) => new Formula.Power(x,D(n));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(P(x),FormulaLogicOperator.And,P(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(P(x),FormulaLogicOperator.Implies,P(y));
    private static Formula GroundSpaceFormula()
    {
        var shifted = Sub(Call("hamiltonian", S),
            Mul(Call("ofReal", Call("groundEnergy", S)), D(1)));
        return Spin(Equal(Call("groundSpace", S),
            Call("inf", Call("ker", shifted), Call("zeroWeightSpace", S))));
    }
    private static Formula ClaimFormula() => new Formula.Logic(Call("claim"),FormulaLogicOperator.Iff,
        Spin(Imp(LE(D(1),S), And(
            All(V,Call("V",S),Imp(And(Mem(V,Call("singletSpace",S)),Equal(Call("norm",V),D(1))),
                LE(Call("singletLowerBound",S),Call("re",Call("inner",V,Mul(Call("hamiltonian",S),V)))))),
            And(LT(Call("groundEnergy",S),Call("singletLowerBound",S)),
                Equal(Call("inf",Call("groundSpace",S),Call("singletSpace",S)),Call("bottom")))))));
}
