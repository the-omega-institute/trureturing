using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.GraphDensity;

internal sealed class UniqueBasisFormationRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Entanglement/GraphDensity/UniqueBasisFormationRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumChannels/songchendjokovic2023uniquebasis");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonorthogonal ensemble lowers formation on the Song–Chen–Djokovic subspace.",
        H("Formation is not constant on the three-vector subspace"),
        Blocks(
            Paragraph(Text("Coordinates use zero-based Fin indices and complex amplitudes. Real square roots are embedded into the complex numbers. The operation rankOneDensity is Matrix.vecMulVec v (star v); partialTraceRight traces out the second factor. FormationBounds.E_F takes the infimum of finite-ensemble marginal entropy costs, in bits.")),
            Def("G", GFormula(), "Song–Chen–Djokovic, Eq. (2), arXiv v3 p. 2: the displayed conditional expression lists all twelve nonzero entries of G, with row and column indices decreased by one.", AssessedProvenance.FromLiterature(Source)),
            Def("Psi", PsiFormula(), "Eq. (3), arXiv v3 p. 2: |Ψ₁⟩ = |1⟩⊗|r₁⟩ + |2⟩⊗|r₄⟩ + |3⟩⊗|r₇⟩, |Ψ₂⟩ = |1⟩⊗|r₂⟩ + |2⟩⊗|r₅⟩ + |3⟩⊗|r₈⟩, |Ψ₃⟩ = |1⟩⊗|r₃⟩ + |2⟩⊗|r₆⟩ + |3⟩⊗|r₉⟩, where |r_i⟩ is the i-th column vector of G. Thus Psi k (a,b) is the b-entry of column 3a+k; Fin.mk forms its column index and its omitted proof verifies that it is below 9.", AssessedProvenance.FromLiterature(Source)),
            Def("spanPsi", SpanFormula(), "The subspace S is the complex span of Ψ₁, Ψ₂ and Ψ₃. Set.range Psi includes exactly the three zero-based choices of k.", AssessedProvenance.FromLiterature(Source)),
            Def("claim", ClaimFormula(), "Song–Chen–Djokovic, arXiv v3 p. 3: Further, by calculation one can see that every state in the span of the three states has entanglement more than 1.52 ebits. Hence, the entanglement of formation (EOF) of every mixed state whose range is contained in the span is also more than 1.52 ebits [19]. We don't know whether this EOF is exactly equal to that of the pure state |Ψ₁⟩. The matrix rho ranges over all density operators on Fin 3 × Fin 9; positivity, trace one and range inclusion express the source's mixed-state domain. Its comparison state is rankOneDensity(Psi 0).", AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("positive-phase"), DeclarationHandle.Create(Module + "positive_phase"),
                H("Positive-weight components of a pure state differ only by phase"),
                StatementSource.FromAuthor(Disp(PositivePhaseFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For arbitrary natural dimensions p and q, let v be a unit vector and e a finite ensemble whose average is rankOneDensity v. Every component e.psi i with strictly positive weight is z times v for a complex scalar z of norm one. The ensemble's kernel constraints force all two-coordinate minors of v and e.psi i to vanish, so the vectors are proportional; their unit norms fix the modulus of the scalar."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Module + "result"),
                H("The equality fails"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Set Pj=rankOneDensity(Psi j). The density (P0+P1+P2)/3 has range in spanPsi. The four ensemble vectors are (Psi 0 + sqrt(3) • Psi 1)/2, (Psi 0 - sqrt(3) • Psi 1)/2, Psi 0 and Psi 2, with weights 2/9, 2/9, 2/9 and 1/3. The first two marginals have spectrum (17,10,9)/36. Their entropy Hstar is strictly below H0=H(4/9,1/3,2/9), by 2^102 < 17^17·5^10·3^6 and the logarithm laws. The ensemble cost is (4/9)Hstar+(5/9)H0, hence strictly below H0. Every positive-weight component of an ensemble of a unit pure state is a unit phase multiple; zero-weight components vanish from the cost. Thus E_F(P0)=H0, and the finite-ensemble upper bound contradicts claim.")),
                    Paragraph(Text("This supplies a strict upper bound for the density's formation, not its exact infimum. The general positive diagonal-weight family is a neighbouring question. The numerical values H0=1.5304930568, Hstar=1.5244951608 and cost=1.5278273252 are compatible with the source's 1.52-ebit lower bound. These values are computed by the independent experiment check.py in the-omega-institute/trureturing-experiments, commit e0c03b28bb524e37942a1e8ae9687e92ffa7c0ac; they are not decimal kernel conclusions."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("song-chen-djokovic-2023-unique-basis-eof"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Def(string name, Formula formula, string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Module + name),
            H(name), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula lhs, Formula rhs) => new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs);
    private static Formula And(Formula lhs, Formula rhs) => new Formula.Logic(Parenthesized(lhs), FormulaLogicOperator.And, Parenthesized(rhs));
    private static Formula Implies(Formula lhs, Formula rhs) => new Formula.Logic(Parenthesized(lhs), FormulaLogicOperator.Implies, Parenthesized(rhs));
    private static Formula Fin(int n) => Call("Fin", new Formula.Number(n));
    private static Formula ComplexType => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Ambient => Seq(Parenthesized(Fin(3)), Times, Parenthesized(Fin(9)));
    private static Formula MatrixType => Call("Matrix", Ambient, Ambient, ComplexType);
    private static Formula Fraction(int a, int b) => new Formula.Fraction(new Formula.Number(a), new Formula.Number(b));
    private static Formula Sqrt(int n) => ComplexCast(Apply(Qualified("Real", "sqrt"), new Formula.Number(n)));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula ComplexCast(Formula a) => Parenthesized(Seq(a, Colon, ComplexType));
    private static Formula Formation(Formula a) => Apply(Seq(Operatorname, Grp(F.Id("FormationBounds")), Dot, F.Id("E"), Underscore, F.Id("F")), a);

    private static Formula GFormula()
    {
        Formula i=F.Id("i"), j=F.Id("j");
        Formula[] entries = [Fraction(2,3), new Formula.Fraction(D(1),Sqrt(3)),
            new Formula.Fraction(Qualified("Complex","I"),Mul(D(3),Sqrt(3))),
            new Formula.Fraction(D(2),Mul(D(3),Sqrt(3))),new Formula.Fraction(Sqrt(2),D(3)),
            new Formula.Fraction(D(1),Sqrt(3)),new Formula.Fraction(Sqrt(2),D(3)),
            new Formula.Fraction(Sqrt(11),Mul(D(3),Sqrt(3))),
            new Formula.Fraction(Parenthesized(new Formula.Binary(D(3),FormulaBinaryOperator.Add,Mul(D(2),Qualified("Complex","I")))),Mul(D(3),Sqrt(33))),
            new Formula.Fraction(D(1),Sqrt(33)),Fraction(2,3),new Formula.Fraction(D(1),Sqrt(3))];
        (int Row,int Col)[] slots=[(0,0),(1,1),(1,5),(1,6),(2,2),(3,3),(4,4),(5,5),(5,6),(6,6),(7,7),(8,8)];
        Formula rhs=D(0);
        for (int k=slots.Length-1;k>=0;k--)
            rhs=Call("ite",And(Equal(i,new Formula.Number(slots[k].Row)),Equal(j,new Formula.Number(slots[k].Col))),entries[k],rhs);
        return All("i",Fin(9),All("j",Fin(9),Equal(Call("G",i,j),rhs)));
    }

    private static Formula PsiFormula()
    {
        Formula k=F.Id("k"),ab=F.Id("ab");
        Formula column=new Formula.Binary(Mul(D(3),Call("val",Seq(ab,Dot,D(1)))),FormulaBinaryOperator.Add,Call("val",k));
        Formula index=Apply(Qualified("Fin","mk"),column);
        return All("k",Fin(3),All("ab",Ambient,Equal(Apply(Call("Psi",k),ab),Call("G",Seq(ab,Dot,D(2)),index))));
    }

    private static Formula SpanFormula() => Equal(F.Id("spanPsi"),
        Apply(Qualified("Submodule","span"),ComplexType,Apply(Qualified("Set","range"),F.Id("Psi"))));

    private static Formula ClaimFormula()
    {
        Formula rho=F.Id("rho");
        Formula psd=Apply(Qualified("Matrix","PosSemidef"),rho);
        Formula trace=Equal(Apply(Qualified("Matrix","trace"),rho),D(1));
        Formula range=new Formula.Relation(Apply(Qualified("LinearMap","range"),Apply(Seq(Qualified("Matrix","toLin"), Apos),rho)),FormulaRelationOperator.LessThanOrEqual,F.Id("spanPsi"));
        Formula eq=Equal(Formation(rho),Formation(Call("rankOneDensity",Call("Psi",D(0)))));
        return Equal(F.Id("claim"),All("rho",MatrixType,Implies(psd,Implies(trace,Implies(range,eq)))));
    }

    private static Formula PositivePhaseFormula()
    {
        Formula p = F.Id("p"), q = F.Id("q"), v = F.Id("v"), e = F.Id("e");
        Formula i = F.Id("i"), x = F.Id("x"), z = F.Id("z");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula ambient = Seq(Parenthesized(Call("Fin", p)), Times, Sp, Parenthesized(Call("Fin", q)));
        Formula vectors = Seq(Parenthesized(ambient), To, Sp, ComplexType);
        Formula norm(Formula value) => Seq(Vert, Sp, value, Sp, Vert);
        Formula sum = Seq(Sum, Underscore, Grp(Seq(x, Colon, ambient)), Sp,
            norm(Apply(v, x)), Caret, D(2));
        Formula weight = Apply(Seq(e, Dot, Operatorname, Grp(F.Id("weight"))), i);
        Formula component = Apply(Seq(e, Dot, Operatorname, Grp(F.Id("psi"))), i);
        Formula phase = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("z"),
            ComplexType, And(Equal(norm(z), D(1)), Equal(component, Seq(z, Cdot, Sp, v))));
        Formula positive = new Formula.Relation(D(0), FormulaRelationOperator.LessThan, weight);
        return All("p", naturals, All("q", naturals, All("v", vectors,
            Implies(Equal(sum, D(1)), All("e", Call("Ensemble", Call("rankOneDensity", v)),
                All("i", Call("Fin", Seq(e, Dot, Operatorname, Grp(F.Id("N")))),
                    Implies(positive, phase)))))));
    }
}
