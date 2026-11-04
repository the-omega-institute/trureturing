using System.Linq;
using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases.MazorchukXuNormalizationNotation;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal static class MazorchukXuNormalizationNotation
{
    internal static Formula N => Fn("Nat");
    internal static Formula Q => Fn("Rat");
    internal static Formula Prop => Fn("Prop");
    internal static Formula Ty => Fn("Type");
    internal static Formula Pairs => Fn("Prod", N, N);
    internal static Formula Points => Fn("Finset", Pairs);
    internal static Formula V(string name) => F.Id(name);
    internal static Formula Fn(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    internal static Formula Apply(Formula fn, params Formula[] args) =>
        Seq(fn, Open, new Formula.LatexSequence([.. args.SelectMany((a, i) =>
            i == 0 ? new[] { a } : new[] { Comma, Sp, a })]), Close);
    internal static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    internal static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    internal static Formula Many(string names, Formula domain, Formula body)
    {
        foreach (var name in names.Split(' ').Reverse()) body = All(name, domain, body);
        return body;
    }
    internal static Formula Par(Formula a) => Seq(Open, a, Close);
    internal static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Par(a), op, Par(b));
    internal static Formula And(params Formula[] xs) =>
        xs.Aggregate((a, b) => Logic(a, FormulaLogicOperator.And, b));
    internal static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    internal static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    internal static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    internal static Formula Not(Formula a) => Seq(Neg, Sp, Par(a));
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    internal static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    internal static Formula Subset(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    internal static Formula Plus(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    internal static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    internal static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    internal static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    internal static Formula Set(string name, Formula domain, Formula predicate) =>
        Seq(OpenBrace, V(name), Sp, InMacro, Sp, domain, Bar, Sp, predicate, CloseBrace);
    internal static Formula Rel(Formula a) => new Formula.TypeArrow(a, new Formula.TypeArrow(a, Prop));
    internal static Formula Map(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    internal static Formula Ordered(string name, Formula body) =>
        All(name, Ty, Seq(OpenBracket, Fn("LinearOrder", V(name)), CloseBracket, Sp, body));
    internal static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/mazorchukxu2026cokernel");
    internal static DocumentBlock Node(string module, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature = false) =>
        Describe.Lean(DescribeId.Create("mazorchuk-xu-" + module.ToLowerInvariant() + "-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Combinatorics/BinomialBases/MazorchukXu" + module + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}


internal sealed class MazorchukXuNormalizationDocument : IScribeDocumentDefinition
{
    private static Formula I => V("i");
    private static Formula M => V("M");
    private static Formula K => V("k");
    private static Formula Carrier(Formula m) => Fn("CoordinateDataCarrier",m,I);
    private static Formula Data(Formula m) => Fn("coordinateDataFamily",m,I);
    private static Formula U(Formula m) => Fn("erase",Fn("univ",Fn("Fin",Plus(m,Fn("one")))),Fn("zero"));
    private static Formula Support => Fn("coordinateDataSupport",V("d"));
    private static Formula Fiber(Formula m, Formula support) => Fn("filter",Data(m),Fn("supportEquals",support));
    private static Formula Coeff(Formula k) => Fn("patternCoefficient",I,k);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prescribed-support fibers give exact size-independent coefficients for the literal source count. Zero is fixed separately, all ties remain, and every valid original rank is included.",
        H("Exact finite-support normalization and binomial counting"),Blocks(
        Node("Normalization","coordinateDataSupport","Positive support of the two coordinate arrays",
            Many("M i",N,All("d",Carrier(M),Eq(Support,Fn("erase",Fn("union",Fn("image",Fn("fst",V("d"))),Fn("image",Fn("fst",Fn("snd",V("d"))))),Fn("zero"))))),
            "Both images range over Fin i. Remove zero from their union; no strictness, positivity or distinctness is assumed for either coordinate array. Its cardinality is bounded by 2i.",DescribeRole.Definition),
        Node("Normalization","patternCoefficient","The admissible full-support coefficient",
            Many("i k",N,Eq(Coeff(K),Fn("card",Fiber(K,U(K))))),
            "At ordinary size k count exactly those admissible data using every positive coordinate from 1 through k. Ordered exceptional bits remain part of the datum, rather than being assumed unique. The coefficient is a natural number independent of n.",DescribeRole.Definition),
        Node("Normalization","coordinateDataSupport_fiber_card","Every prescribed support has the same coefficient",
            Many("M i",N,All("S",Fn("Finset",Fn("Fin",Plus(M,Fn("one")))),Imp(Subset(V("S"),U(M)),Eq(Fn("card",Fiber(M,V("S"))),Coeff(Fn("card",V("S"))))))),
            "Mathlib orderIsoOfFin enumerates insert 0 S increasingly and fixes zero. Apply that embedding pointwise to positions and cutoffs, retaining the exceptional bits. Extending the finite embedding to a strictly increasing natural map allows direct use of coordinate_rules_refinement_iff and coordinate_rules_bounded_iff. The inverse uses the same order isomorphism on the actual two coordinate images. These two maps give a bijection of the prescribed support fibers, including S empty.",DescribeRole.Theorem),
        Node("Normalization","count_eq_binomial_sum","Literal count as a finite binomial sum",
            Many("n i",N,Imp(Le(I,Plus(V("n"),Fn("one"))),Eq(Fn("count",V("n"),Sub(Plus(V("n"),Fn("one")),I)),Fn("sum",Fn("range",Plus(Mul(Fn("two"),I),Fn("one"))),Fn("lambda",K,Mul(Coeff(K),Fn("choose",Sub(Plus(V("n"),Fn("one")),I),K))))))),
            "Group the actual coordinate family first by support cardinality and then by its prescribed support. The support has at most 2i values. The upstream powerset-cardinality theorem counts the k-subsets of the M positive ordinary ranks by choose(M,k). The prescribed-support bijection supplies the common fiber cardinality. Finally count_eq_coordinateDataFamily_card returns this identity to the literal repeated-point source count for every i<=n+1. No eventual threshold, genericity premise or negative rank occurs. The factorial value of the top coefficient is a separate obligation.",DescribeRole.Theorem)),[]));
}
