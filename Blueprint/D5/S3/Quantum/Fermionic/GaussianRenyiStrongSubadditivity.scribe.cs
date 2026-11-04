using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class GaussianRenyiStrongSubadditivityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Fermionic/GaussianRenyiStrongSubadditivity";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Entropy/camilolandieliens2019renyissa");

    private static Formula X(string name) => name == "α" ? Alpha : F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Local(string name, params Formula[] args) => At(Qualified(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula size) => At(Qualified("Fin"), size);
    private static Formula Indices => Seq(Parenthesized(FinOf(X("n"))), Sp, Times, Sp, Parenthesized(FinOf(D(2))));
    private static Formula MatrixOf(Formula indices) => At(Qualified("Matrix"), indices, indices, Reals);
    private static Formula ModeSets => At(Qualified("Finset"), FinOf(X("n")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Smul(Formula scalar, Formula matrix) => Seq(Parenthesized(scalar), Sp, Cdot, Sp, Parenthesized(matrix));
    private static Formula Negate(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula HermitianMatrix => Smul(Qualified("Complex", "I"),
        At(Qualified("Matrix", "map"), X("G"), Qualified("Complex", "ofReal")));
    private static Formula HermitianCondition => At(Qualified("Matrix", "IsHermitian"), HermitianMatrix);
    private static Formula Eigenvalue => At(Qualified("Matrix", "IsHermitian", "eigenvalues"), X("h"), X("i"));
    private static Formula ReducedIndices => At(Qualified("Subtype"), LambdaOf("p", Indices,
        Member(At(Qualified("Prod", "fst"), X("p")), X("X"))));
    private static Formula PhysicalDefinition() => All("n", Naturals, All("G", MatrixOf(Indices),
        Equal(Local("physicalCovariance", X("G")),
            And(Equal(At(Qualified("Matrix", "transpose"), X("G")), Negate(X("G"))),
                Some("h", HermitianCondition, All("i", Indices, LE(new Formula.Absolute(Eigenvalue), D(1))))))));
    private static Formula EntropyDefinition()
    {
        Formula summand = At(Qualified("D5", "S3", "Quantum", "Analysis", "FermionicRenyiStieltjes", "fermionicRenyiFunction"),
            Alpha, Eigenvalue);
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(X("i"), Colon, Sp, ReducedIndices)), Sp, Parenthesized(summand));
        Formula conditional = At(Qualified("dite"), HermitianCondition,
            LambdaOf("h", HermitianCondition, Mul(Typed(new Formula.Fraction(D(1), D(2)), Reals), sum)),
            At(Qualified("Function", "const"), new Formula.Not(Parenthesized(HermitianCondition)), Typed(D(0), Reals)));
        return All("n", Naturals, All("X", ModeSets, All("α", Reals, All("G", MatrixOf(ReducedIndices),
            Equal(Typed(Local("fermionicGaussianRenyiEntropy", Alpha, X("G")), Reals), conditional)))));
    }
    private static Formula Union(Formula left, Formula right) => Seq(Parenthesized(left), Sp, Cup, Sp, Parenthesized(right));
    private static Formula EntropyOn(Formula modes) => Local("fermionicGaussianRenyiEntropy", Alpha,
        At(Qualified("D5", "S3", "Quantum", "Thermal", "GaussianRenyiStrongSubadditivity", "reducedCovariance"), X("G"), modes));
    private static Formula ClaimFormula()
    {
        Formula A = X("A");
        Formula B = X("B");
        Formula C = X("C");
        Formula inequality = new Formula.Relation(Add(EntropyOn(Union(A, B)), EntropyOn(Union(B, C))),
            FormulaRelationOperator.GreaterThanOrEqual, Add(EntropyOn(Union(Union(A, B), C)), EntropyOn(B)));
        Formula orders = All("α", Reals, Imp(LT(D(0), Alpha), Imp(LT(Alpha, D(1)), inequality)));
        return All("n", Naturals, All("G", MatrixOf(Indices), Imp(Local("physicalCovariance", X("G")),
            All("A", ModeSets, All("B", ModeSets, All("C", ModeSets,
                Imp(At(Qualified("Disjoint"), A, B), Imp(At(Qualified("Disjoint"), A, C),
                    Imp(At(Qualified("Disjoint"), B, C), orders)))))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fermionic Gaussian Renyi covariance entropy satisfies strong subadditivity for every real order strictly between zero and one.",
        H("Strong subadditivity of fermionic Gaussian Renyi entropy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("physical-covariance"), DeclarationHandle.Create(Module + ".physicalCovariance"),
                H("Physical fermionic covariances"), StatementSource.FromAuthor(Disp(PhysicalDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A covariance is a real antisymmetric matrix on the two Majorana indices of each mode. Multiplication by i after embedding its entries into the complex numbers gives a Hermitian matrix whose real eigenvalues have absolute value at most one. This encodes the fermionic covariance condition and the paired spectrum described by Camilo, Landi and Eliëns (RenyiGaussian_v2.tex, lines 265–285)."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fermionic-gaussian-renyi-entropy"), DeclarationHandle.Create(Module + ".fermionicGaussianRenyiEntropy"),
                H("Entropy from the full Majorana spectrum"), StatementSource.FromAuthor(Disp(EntropyDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For a matrix on the Majorana indices of a mode set X, take one half of the sum of fermionicRenyiFunction over every eigenvalue of iG. The two signs of each mode contribute the same scalar entropy, so this is Eq. renyi_fermionic_1, equivalently Eq. renyi_fermionic_3 (RenyiGaussian_v2.tex, lines 297–320). The definition assigns zero if iG is not Hermitian and also gives zero on an empty index type."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Module + ".claim"),
                H("The fermionic strong subadditivity proposition"),
                StatementSource.FromAuthor(Disp(Equal(Qualified("claim"), Parenthesized(ClaimFormula())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every physical covariance and every three pairwise disjoint mode sets A, B and C, the AB and BC entropies sum to at least the ABC and B entropies for 0<α<1. The principal blocks are given by D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.reducedCovariance, which retains both Majorana indices of every selected mode. The source conjectures validity on [0,1] rather than asserting a proof (RenyiGaussian_v2.tex, line 498); its conditional mutual information is Eq. RCMI, lines 122–125. This proposition covers the open interval using the covariance entropy formula. The endpoint orders, a density-operator construction and non-Gaussian states are outside the statement."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("Strong subadditivity of the covariance entropy"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Antisymmetry of the real covariance makes iG Hermitian. Unitary diagonalization identifies the eigenvalues of I+iuG as 1+uλ, where λ ranges over the eigenvalues of iG. The spectral bound gives positive semidefiniteness at u=1. The identity I+iuG=u(I+iG)+(1−u)I and shifted_posDef then give positive definiteness for 0≤u<1. Principal restriction commutes with the interpolation. Positivity at u=1 and u=−1 passes to each principal block and bounds its Hermitian eigenvalues between minus one and one; antisymmetry also passes to these blocks. Here each reduction is the principal block supplied by D5.S3.Quantum.Thermal.GaussianRenyiStrongSubadditivity.reducedCovariance.")),
                    Paragraph(Text("The spectral determinant identity det_spectral gives det(I+iuG) as the product of the factors 1+uλ over the eigenvalues λ of iG. Transposition changes u to −u without changing the determinant. Multiplying the spectral products at u and −u expresses det(I+iuG) squared as the product of the factors 1−u²λ². Each such factor and the determinant are positive for 0≤u<1. Taking logarithms gives log(det(I+iuG)) as one half of the sum of these scalar logarithms.")),
                    Paragraph(Text("Apply stieltjes_representation to each eigenvalue of the reduced covariance. Its integrable logarithmic integrand permits interchange of the finite sum and integral. There are twice as many Majorana indices as selected modes, by reduced_card. Consequently the entropy of a block X is |X| log 2 plus the integral on (0,1) of fermionicWeight(α,u) times log(det(I+iuG_X)). This is the positive Stieltjes mixture S_α(G_X)=|X| ln 2+∫₀¹ v_α(u) ln det(I+iuG_X) du, with v_α given by fermionicWeight. It includes pure modes because the scalar representation includes both spectral endpoints.")),
                    Paragraph(Text("For each u in (0,1), apply log_koteljanskii to the Hermitian positive definite matrix I+iuG and the three disjoint Majorana index sets A×Fin 2, B×Fin 2 and C×Fin 2. The four principal determinants on ABC, B, AB and BC agree with the determinants of the corresponding reduced interpolations, since their index subtypes are equivalent. Thus the ABC and B logarithms sum to at most the AB and BC logarithms. Multiply by the strictly positive fermionicWeight and integrate. Integrability of all four weighted logarithms justifies splitting the integrals. Finally, |A∪B|+|B∪C|=|A∪B∪C|+|B|, also after casting these natural cardinalities to the real numbers, cancels the multiples of log 2 in the four mixture identities. The remaining inequality is the asserted strong subadditivity."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("camilo-landi-eliens-2019-fermionic-gaussian-renyi-strong-subadditivity"),
                    ResolutionKind.Proved)))));
}
