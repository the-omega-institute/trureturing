using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class StructuredNegativityCoincidenceRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/StructuredNegativityCoincidenceRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/kumari2022structured");
    private const string Conjecture = "For d ⊗ d dimensional state, we conjecture from the result obtained in this work that negativity coincide with the structured negativity when the number of negative eigenvalues of the partially transposed matrix is equal to d(d−1)/2.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The pure state (|00⟩ + 2|11⟩ + 2|22⟩)/3 has three negative partial-transpose eigenvalues, but negativity 8/9 and structured negativity 4/3. It refutes the coincidence conjecture of Kumari and Adhikari.",
        H("Negativity and structured negativity differ for a pure two-qutrit state"),
        Blocks(
            Node("partialTransposeB", "Partial transpose on B", PartialFormula(),
                "The basis indices are pairs in Fin d × Fin d for C^d ⊗ C^d. Partial transposition exchanges the second row and column coordinates, leaving the first coordinates in place.", true),
            Node("IsDensity", "Density matrices", Disp(All(Dim,Nats,All(Rho,Matrices,Iff(Call("IsDensity", Rho),
                And(Call("PosSemidef", Rho), Eq(Call("trace", Rho), D(1))))))),
                "A density matrix is positive semidefinite and has trace one; positivity is Mathlib's complex Hermitian positive semidefiniteness.", true),
            Node("eigenvalues", "Hermitian eigenvalues with multiplicity", EigenFormula(),
                "For a Hermitian matrix A, let h be its Hermitian proof and let h.eigenvalues be Mathlib's real eigenvalue function on Fin d × Fin d. The multiset maps every element of this index type to its eigenvalue, retaining duplicates. Matrix.IsHermitian.roots_charpoly_eq_eigenvalues identifies its complex image with the characteristic-polynomial roots, including algebraic multiplicity. For a non-Hermitian matrix this definition returns the empty multiset; this extension is not used for the density matrix or its partial transpose and SPA below.", false),
            Node("negCount", "Count of negative eigenvalues", Disp(All(Dim,Nats,All(A,Matrices,Eq(Call("negCount", A),
                Call("card", Negative(A)))))),
                "The source states (p. 4): 'Let us suppose that (I ⊗ T)ρ has q (≤ (d−1)^2) number of negative eigenvalues'. Here q counts strictly negative eigenvalues with multiplicity, rather than distinct numerical values.", true),
            Node("negativity", "Negativity", NegativityFormula(),
                "Equation (6), p. 2: 'N(ρ) = (‖ρ^{T_B}‖_1 − 1)/(d−1) = (2/(d−1)) Σ_{λ_i<0} |λ_i(ρ^{T_B})| where ‖.‖_1 denotes trace norm and ρ^{T_B} is the partial transposition of the density matrix ρ.' The definition uses the displayed eigenvalue-sum form. The sum traverses the negative-eigenvalue multiset, so repeats contribute repeatedly. The real cast of d is taken before subtracting 1. Typed val occurrences denote the indicated natural-number coercions to the real or complex numbers.", true),
            Node("spaPT", "Structural physical approximation", SpaFormula(),
                "Equation (7), p. 2: 'For d ⊗ d system described by the density operator ρ, the SPA-PT of the state ρ denoted as ρ̃ and it may be expressed as [32],' followed by ρ̃ = (d/(d^3+1)) I⊗I + (1/(d^3+1)) [I⊗T](ρ). The identity on the pair-indexed space is I⊗I; the coefficients in Lean are complex scalar multiples.", true),
            Node("leastEigenvalue", "Least eigenvalue", Disp(All(Dim,Nats,All(A,Matrices,Eq(Call("leastEigenvalue", A),
                Call("sInf", Call("toSet", Call("eigenvalues", A))))))),
                "The source states (p. 3): 'where λ_min(ρ̃) denote the minimum eigenvalue of ρ̃.' The least real eigenvalue is the infimum of the underlying set of the eigenvalue multiset. For Hermitian matrices of positive dimension the set is finite and nonempty, so this is its minimum. Multiplicity is irrelevant for the minimum.", true),
            Node("structuredNegativity", "Structured negativity", StructuredFormula(),
                "Equation (9), p. 3: 'N_S(ρ) = K.max{d/(d^3+1) − λ_min(ρ̃),0} where K = d(d^3+1).' Lean uses precisely this scale, threshold and maximum, with leastEigenvalue applied to spaPT. All divisions in this formula are real divisions.", true),
            Node("claim", "The Kumari–Adhikari coincidence conjecture", ClaimFormula(),
                "Abstract, p. 1: '" + Conjecture + "' Conclusion, p. 7: 'Thus, we conjecture that the negativity and structured negativity coincides when q=d(d−1)/2.' Encoding: d is a natural number at least two, rho is an arbitrary density matrix on C^d ⊗ C^d, and q is negCount(partialTransposeB(rho)). natDiv denotes natural-number division, equal to the floor of the nonnegative quotient; subtraction in d−1 here is natural subtraction. The conclusion equates the two real quantities with the normalizations in equations (6) and (9).", true),
            Node("result", "Refutation by a pure 3⊗3 state", Disp(new Formula.Not(F.Id("claim"))),
                "Take ψ=(|00⟩+2|11⟩+2|22⟩)/3 and ρ=|ψ⟩⟨ψ|. The partial transpose is Hermitian with eigenvalue multiset {1/9,2/9,2/9,−2/9,4/9,4/9,−2/9,−4/9,4/9}. Thus q=3=3(3−1)/2 and N=8/9. Its SPA has eigenvalues {7/63,29/252,29/252,25/252,31/252,31/252,25/252,23/252,31/252}, with minimum 23/252, giving N_S=84 max{3/28−23/252,0}=4/3. The eigenvalues follow from an explicit rational change of basis: diagonal coordinates use |ii⟩, and each off-diagonal pair uses |ij⟩+|ji⟩ and |ij⟩−|ji⟩. Similarity preserves the characteristic polynomial; Mathlib's spectral theorem relates its roots to the Hermitian eigenvalue multiset. Since 8/9 differs from 4/3, the conjecture fails.", false, DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kumari-adhikari-2022-structured-negativity-coincidence-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        bool literature, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("sneg-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Rho => F.Id("rho");
    private static Formula A => F.Id("A");
    private static Formula Dim => F.Id("d");
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Named(string n) => Seq(Operatorname, Grp(F.Id(n)));
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Named(n), [.. args]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Eq(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, Parenthesized(y));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, y);
    private static Formula All(Formula x, Formula domain, Formula body) => Seq(Forall, Sp, x, Colon, domain, Comma, Sp, body);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, byte n) => new Formula.Power(x, D(n));
    private static Formula Pair(Formula x, Formula y) => Parenthesized(Seq(x, Comma, y));
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Indices => Seq(Call("Fin", Dim), Sp, F.Times, Sp, Call("Fin", Dim));
    private static Formula Matrices => Call("Matrix", Indices, Indices, Complexes);
    private static Formula RealDim => Parenthesized(Seq(Call("val",Dim),Colon,Reals));
    private static Formula Negative(Formula matrix) => Call("filter", Seq(F.Id("x"), Sp, Mapsto, Sp, Rel(F.Id("x"), FormulaRelationOperator.LessThan, D(0))), Call("eigenvalues", matrix));
    private static Formula PartialFormula()
    {
        Formula i=F.Id("i"), j=F.Id("j"), k=F.Id("k"), l=F.Id("l");
        return Disp(All(Dim,Nats,All(Rho,Matrices,
            All(i,Call("Fin",Dim),All(j,Call("Fin",Dim),All(k,Call("Fin",Dim),All(l,Call("Fin",Dim),
                Eq(new Formula.Apply(Call("partialTransposeB", Rho), [Pair(i,j), Pair(k,l)]),
                    new Formula.Apply(Rho, [Pair(i,l), Pair(k,j)])))))))));
    }
    private static Formula EigenFormula() => Disp(And(
        All(Dim,Nats,All(A,Matrices,All(F.Id("h"),Call("IsHermitian",A),
            Eq(Call("eigenvalues",A),Call("map",Seq(F.Id("h"),Dot,F.Id("eigenvalues")),
                Call("val",Parenthesized(Seq(Seq(Operatorname,Grp(F.Id("Finset"),Dot,F.Id("univ"))),Colon,Call("Finset",Indices))))))))),
        All(Dim,Nats,All(A,Matrices,Imp(new Formula.Not(Call("IsHermitian",A)),Eq(Call("eigenvalues",A),D(0)))))));
    private static Formula NegativityFormula() => Disp(All(Dim,Nats,All(Rho,Matrices,Eq(Call("negativity", Dim, Rho),
        Mul(new Formula.Fraction(D(2), Sub(RealDim, D(1))),
            Call("sum", Call("map", Named("abs"), Negative(Call("partialTransposeB", Rho)))))))));
    private static Formula SpaFormula() => Disp(All(Dim,Nats,All(Rho,Matrices,Eq(Call("spaPT", Rho),
        Add(Mul(new Formula.Fraction(Parenthesized(Seq(Call("val",Dim),Colon,Complexes)), Add(Pow(Parenthesized(Seq(Call("val",Dim),Colon,Complexes)),3),D(1))), D(1)),
            Mul(new Formula.Fraction(D(1), Add(Pow(Parenthesized(Seq(Call("val",Dim),Colon,Complexes)),3),D(1))), Call("partialTransposeB", Rho)))))));
    private static Formula StructuredFormula() => Disp(All(Dim,Nats,All(Rho,Matrices,Eq(Call("structuredNegativity", Dim, Rho),
        Mul(Mul(RealDim, Parenthesized(Add(Pow(RealDim,3),D(1)))),
            Call("max", Sub(new Formula.Fraction(RealDim,Add(Pow(RealDim,3),D(1))),
                Call("leastEigenvalue", Call("spaPT", Rho))), D(0)))))));
    private static Formula ClaimFormula() => Disp(Iff(F.Id("claim"),
        All(Dim,Nats,All(Rho,Matrices,Imp(Rel(D(2),FormulaRelationOperator.LessThanOrEqual,Dim),
            Imp(Call("IsDensity",Rho),Imp(
                Eq(Call("negCount",Call("partialTransposeB",Rho)),
                    Call("natDiv",Mul(Dim,Parenthesized(Sub(Dim,D(1)))),D(2))),
                Eq(Call("negativity",Dim,Rho),Call("structuredNegativity",Dim,Rho)))))))));
}
