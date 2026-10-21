using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsoluteSeparability;

internal sealed class LouvetSymmetricAbsolutelyPPTDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/AbsoluteSeparability/LouvetSymmetricAbsolutelyPPT.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumContext/louvet2025symmetricppt");
    private const string ConjectureQuote = "Conjecture 1 (p. 3): “Any symmetric N-qudit state ρ with a spectrum composed of D = binom(N+d−1, d−1) non-zero eigenvalues of the form (1 − (D−1)p/D, p/D, …, p/D), with p ∈ [p_min, 1] where p_min = 1/(1 + 2[D binom(N, ⌊N/2⌋)]^{−1}), is SAPPT.”";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The conjectured symmetric qudit spectrum is SAPPT at and above its threshold.", H("Symmetric qudit states with an absolutely PPT spectrum"), Blocks(
            Describe.Lean(DescribeId.Create("lsappt-issymmetricoperator"), DeclarationHandle.Create(Prefix + "IsSymmetricOperator"),
                H("Symmetric operators"), StatementSource.FromAuthor(Disp(OperatorFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The source states on p. 1: “They satisfy ρ = πρπ′ with π and π′ any pair of permutation operators.” For a Hermitian matrix, the column condition expresses support in the symmetric subspace."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lsappt-issymmetricunitary"), DeclarationHandle.Create(Prefix + "IsSymmetricUnitary"),
                H("Symmetric unitaries"), StatementSource.FromAuthor(Disp(UnitaryFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The source states on p. 2: “A symmetric state ρ is said to be symmetric absolutely PPT (SAPPT) [20] if UρU† is PPT for any U ∈ SU(N + 1) [24].” The full tensor-space unitary restricts to a unitary on the symmetric subspace; the indices here allow d local levels."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lsappt-isfullyppt"), DeclarationHandle.Create(Prefix + "IsFullyPPT"),
                H("Every partial transpose is positive"), StatementSource.FromAuthor(Disp(PPTFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The source states on p. 1: “In this work, we are interested in states that are PPT for any bipartition, and we will call them just as PPT states.” Partial transposition is tested on every subset of sites, including the empty and full subsets."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lsappt-issappt"), DeclarationHandle.Create(Prefix + "IsSAPPT"),
                H("Symmetric absolute PPT"), StatementSource.FromAuthor(Disp(SAPPTFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The source states on p. 2: “A symmetric state ρ is said to be symmetric absolutely PPT (SAPPT) [20] if UρU† is PPT for any U ∈ SU(N + 1) [24].” Positivity is required for every subset of tensor sites; scalar phases cancel in unitary conjugation."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lsappt-d"), DeclarationHandle.Create(Prefix + "D"),
                H("Symmetric-space dimension"), StatementSource.FromAuthor(Disp(DimensionFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(ConjectureQuote + " The dimension uses natural subtraction on both arguments."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lsappt-pmin"), DeclarationHandle.Create(Prefix + "pmin"),
                H("Threshold"), StatementSource.FromAuthor(Disp(ThresholdFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(ConjectureQuote + " Nat.div N 2 is the floor of N/2."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lsappt-claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Conjecture 1"), StatementSource.FromAuthor(Disp(ClaimDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(ConjectureQuote + " The indices are all functions from Fin N to Fin d. The full-space characteristic polynomial includes d^N − D zero eigenvalues. N and d are at least two. Natural-number division in the threshold is Nat.div."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lsappt-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Conjecture 1 holds"), StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The permutation symmetrizer retains a positive floor after partial transposition. A positive residual contributes at least minus half its trace on the local symmetric subspace. The spectral parameters and the central binomial coefficient make their sum positive for every bipartition."))), DescribeRole.Theorem))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Q(params string[] names) => Seq(Operatorname,
        Grp(Seq([.. names.SelectMany((name, index) => index == 0
            ? new Formula[] { X(name) } : new Formula[] { Dot, X(name) })])));
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Arr(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula Eqn(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leqf(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Andf(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Ifff(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Plusf(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Minusf(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Timesf(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula left, Formula right) => new Formula.Power(Parenthesized(left), right);
    private static Formula Rat(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Inv(Formula value) => Pow(value, new Formula.Negate(D(1)));
    private static Formula Nats => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(X("C")));

    private static Formula Matrix(Formula index) => At(Q("Matrix"), index, index, Complexes);
    private static Formula Fn(string variable, Formula type, Formula body) => Seq(Q("fun"), Sp, Typed(X(variable), type), Sp, Mapsto, Sp, body);


    private static Formula Fin(Formula size) => At(Q("Fin"), size);
    private static Formula Sites => Arr(Fin(X("N")), Fin(X("d")));
    private static Formula SiteTypes(Formula body) => All("N", Nats, All("d", Nats, body));
    private static Formula Local(string owner, string name, params Formula[] args) => At(Q("D5", "S3", "Quantum", "Entanglement", "AbsoluteSeparability", owner, name), args);
    private static Formula PT(Formula s, Formula a) => Local("SymmetricAbsolutePPTPureBound", "partialTransposeOn", s, a);
    private static Formula PSD(Formula a) => At(Q("Matrix", "PosSemidef"), a);

    private static Formula MulVec(Formula a, Formula v) => At(Q("Matrix", "mulVec"), a, v);
    private static Formula Adj(Formula a) => At(Q("Matrix", "conjTranspose"), a);
    private static Formula Sym(Formula v) => Local("SymmetricAbsolutePPTPermutationFloor", "IsSymmetricVector", v);



    private static Formula Current(string name, params Formula[] args) => Local("LouvetSymmetricAbsolutelyPPT", name, args);
    private static Formula Dim => Current("D", X("N"), X("d"));
    private static Formula Threshold => Current("pmin", X("N"), X("d"));
    private static Formula Choose(Formula n, Formula k) => At(Q("Nat", "choose"), n, k);
    private static Formula DimensionFormula() => SiteTypes(Eqn(Dim,
        Choose(Minusf(Plusf(X("N"), X("d")), D(1)), Minusf(X("d"), D(1)))));
    private static Formula ThresholdFormula() => SiteTypes(Eqn(Threshold,
        Rat(D(1), Plusf(D(1), Timesf(D(2), Inv(Timesf(Typed(Dim, Reals),
            Typed(Choose(X("N"), At(Q("Nat", "div"), X("N"), D(2))), Reals))))))));
    private static Formula OperatorFormula() => SiteTypes(All("rho", Matrix(Sites),
        Ifff(Current("IsSymmetricOperator", X("rho")), All("y", Sites,
            Sym(Fn("x", Sites, At(X("rho"), X("x"), X("y"))))))));
    private static Formula UnitaryFormula() => SiteTypes(All("U", Matrix(Sites),
        Ifff(Current("IsSymmetricUnitary", X("U")), Andf(
            new Formula.Relation(X("U"), FormulaRelationOperator.MemberOf, At(Q("Matrix", "unitaryGroup"), Sites, Complexes)),
            All("v", Arr(Sites, Complexes), Imp(Sym(X("v")), Sym(MulVec(X("U"), X("v")))))))));
    private static Formula PPTFormula() => SiteTypes(All("rho", Matrix(Sites),
        Ifff(Current("IsFullyPPT", X("rho")), All("S", At(Q("Finset"), Fin(X("N"))), PSD(PT(X("S"), X("rho")))))));
    private static Formula SAPPTFormula() => SiteTypes(All("rho", Matrix(Sites),
        Ifff(Current("IsSAPPT", X("rho")), All("U", Matrix(Sites),
            Imp(Current("IsSymmetricUnitary", X("U")), Current("IsFullyPPT",
                Timesf(Timesf(X("U"), X("rho")), Adj(X("U")))))))));
    private static Formula ClaimBody()
    {
        var a = Rat(X("p"), Typed(Dim, Reals));
        var b = Minusf(D(1), Rat(Timesf(Minusf(Typed(Dim, Reals), D(1)), X("p")), Typed(Dim, Reals)));
        Formula Factor(Formula value) => Parenthesized(Minusf(Q("Polynomial", "X"), At(Q("Polynomial", "C"), Typed(value, Complexes))));
        var characteristic = Eqn(At(Q("Matrix", "charpoly"), X("rho")),
            Timesf(Timesf(Factor(b), Pow(Factor(a), Minusf(Dim, D(1)))),
                Pow(Q("Polynomial", "X"), Minusf(Pow(X("d"), X("N")), Dim))));
        return SiteTypes(Imp(Leqf(D(2), X("N")), Imp(Leqf(D(2), X("d")), All("p", Reals,
            Imp(Leqf(Threshold, X("p")), Imp(Leqf(X("p"), D(1)), All("rho", Matrix(Sites),
                Imp(PSD(X("rho")), Imp(Current("IsSymmetricOperator", X("rho")),
                    Imp(characteristic, Current("IsSAPPT", X("rho"))))))))))));
    }
    private static Formula ClaimDefinition() => Ifff(Current("claim"), ClaimBody());

}
