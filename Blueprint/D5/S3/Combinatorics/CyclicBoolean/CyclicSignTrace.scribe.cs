using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CyclicBoolean;

internal sealed class CyclicSignTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CyclicBoolean/CyclicSignTrace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The cyclic Boolean map has an explicit inverse at every positive odd length. Integer Walsh inversion supplies nonempty spectral support.",
        H("Odd cyclic Boolean inversion and the sign-matrix trace"),
        Blocks(
            Node("Word", "Binary words on a cyclic index set", StatementSource.WithoutFormula(),
                "A word of length n is a function from ZMod n to the binary field ZMod 2. All additions in an index are modulo n; all additions in a word value are modulo two.", DescribeRole.Definition),
            Node("chi", "The forward cyclic map", StatementSource.WithoutFormula(),
                "At index i, chi(x) is x_i + x_(i+2) + x_(i+1) x_(i+2). Repeated indices denote the same variable, including at length one.", DescribeRole.Definition),
            Node("sign", "Integer signs", StatementSource.WithoutFormula(),
                "The sign of a binary field element z is the integer (-1) raised to its representative z.val, which is zero or one.", DescribeRole.Definition),
            Node("sourceMatrix", "The literal source matrix", StatementSource.WithoutFormula(),
                "For arbitrary binary words b and a and cyclic index k, the entry at binary row s and column t is sign((a_k + a_(k-2) + b_k)s + a_(k-1)st). The first row is (1,1); the second is ((-1)^h_k,(-1)^(h_k+g_k)), with g_k=a_(k-1) and h_k=a_k+a_(k-2)+b_k.", DescribeRole.Definition),
            Node("sourceTrace", "The ordered integer trace", StatementSource.WithoutFormula(),
                "Form the list of source matrices at representatives zero through n-1 in that order, multiply the list, and take its integer matrix trace. No commutation of matrix factors is used.", DescribeRole.Definition),
            Node("traceSupport", "Nonzero trace support", StatementSource.WithoutFormula(),
                "The trace support consists of every a for which the literal ordered integer trace is nonzero. No word a is excluded.", DescribeRole.Definition),
            Node("claim", "The full affine-support question", StatementSource.WithoutFormula(),
                "For every natural m and every nonzero b of length 2m+1, the direction of the affine span over ZMod 2 of the trace support has dimension at least 2m. The parameter m runs from zero, so this is exactly all positive odd lengths, including length one. The inequality is a lower bound, not an equality. This definition states the question; the inverse and Walsh results below do not prove it.", DescribeRole.Definition),
            Node("alternatingPrefix", "Alternating products", StatementSource.WithoutFormula(),
                "The alternating prefix at i of length t is the product, for r from zero through t-1, of 1+y_(i+2r+1). The empty product is one.", DescribeRole.Definition),
            Node("inverse", "The inverse polynomial", StatementSource.WithoutFormula(),
                "At length 2m+1, the inverse coordinate at i is the sum, for r from zero through m, of y_(i+2r) times the alternating prefix at i of length r. Thus its first term is y_i.", DescribeRole.Definition),
            Node("inverse_spec", "Both inverse identities at every positive odd length", StatementSource.FromAuthor(InverseFormula()),
                "For every m, applying the inverse polynomial after chi gives the original word, and applying chi after the inverse polynomial does the same. The proof does not assume either identity or invertibility.", DescribeRole.Theorem),
            Paragraph(Text("Write y=chi(x). The local Boolean identity is x_i=y_i+(1+y_(i+1))x_(i+2). Iterating t times gives the first t terms of the inverse polynomial plus the alternating prefix of length t times x_(i+2t). For t=m+1 the latter x-coordinate is x_(i+1). If this tail were nonzero, x_(i+1) would be one and the m+1 alternating y-coordinates would all vanish. At each of these positions the recurrence forces the next intervening y-coordinate to vanish and the next x-coordinate in steps of two to be one. The even and odd representatives together cover the cycle, hence y=0.")),
            Paragraph(Text("When chi(x)=0 the recurrence makes x invariant under addition of two. Multiplication by m+1 is an inverse to multiplication by two modulo 2m+1, so every index is reached and x is constant. The image under chi of a constant binary word is that same constant word. Thus the zero fiber contains only the zero word, contradicting the tail's x-coordinate being one. This proves the left inverse identity. The finite domain and codomain have the same cardinality, so injectivity gives surjectivity and hence the right inverse identity.")),
            Node("dot", "Binary dot products", StatementSource.WithoutFormula(),
                "The dot product of a and x is the sum over all cyclic indices of a_i x_i in ZMod 2.", DescribeRole.Definition),
            Node("walsh", "Unnormalized integer Walsh coefficients", StatementSource.WithoutFormula(),
                "For any Boolean function f on the entire binary word space, its coefficient at a is the integer sum over every x of sign(f(x)+dot(a,x)).", DescribeRole.Definition),
            Node("walsh_inversion", "Exact integer Walsh inversion", StatementSource.FromAuthor(InversionFormula()),
                "For every positive length n, every Boolean f and every word y, summing walsh(f,a) sign(dot(a,y)) over all a gives the number of binary words times sign(f(y)). Character orthogonality is applied to an actual AddChar into the integers; this is an integer identity without a choice of normalization.", DescribeRole.Theorem),
            Node("walsh_support_nonempty", "The spectral support is nonempty", StatementSource.FromAuthor(NonemptyFormula()),
                "At every positive length, every Boolean f has a nonzero integer Walsh coefficient. Otherwise inversion at the zero word would equate zero to the nonzero product of the number of words and an integer sign.", DescribeRole.Theorem),
            Node("inverseComponent", "An arbitrary component of the inverse", StatementSource.WithoutFormula(),
                "For arbitrary mask b at length 2m+1, the inverse component at y is dot(b,inverse(m,y)). The mask is unrestricted in this definition.", DescribeRole.Definition),
            Node("inverse_phase_sum", "The exact inverse-component orientation", StatementSource.FromAuthor(PhaseFormula()),
                "For every m and all masks b,a, the sum over x of sign(dot(b,x)+dot(a,chi(x))) is the Walsh coefficient at a of the inverse component associated with b. Reindex by the proved bijection chi and use its left inverse identity. Zero and all-one masks are included.", DescribeRole.Theorem),
            Node("inverse_phase_support_nonempty", "The cyclic Boolean phase support is nonempty", StatementSource.FromAuthor(PhaseNonemptyFormula()),
                "For every natural m and every mask b, some a has a nonzero phase sum over x of sign(dot(b,x)+dot(a,chi(x))). This uses Walsh nonemptiness and the proved inverse reindexing. It is a statement about the phase sum; identification with the literal source trace remains a separate requirement.", DescribeRole.Theorem),
            Paragraph(Text("The literal trace model follows ricardorr, MathOverflow question 512655, original revision E06A6743-2C15-41CD-9390-04D1862ABA02, https://mathoverflow.net/questions/512655, attributed under CC-BY-SA 4.0. The inverse argument above is a direct derivation for this cyclic map.")),
            Paragraph(Text("The affine-support assertion still requires the equality of the ordered matrix trace with the Boolean phase sum, the equivalence between constant derivatives and affine constraints on Walsh support, the corresponding dimension identity, and the complete coefficient classification for every nonzero inverse-component mask. None of these remaining statements is an assumption of the inverse or Walsh theorems above."))
        ), []));

    private static DocumentBlock Node(string name, string title, StatementSource statement, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cyclic-sign-trace-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), statement, AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
    private static Formula Named(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula All(string x, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), t, body);
    private static Formula Some(string x, Formula t, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), t, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Grp(a), FormulaLogicOperator.And, Grp(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Grp(a), FormulaLogicOperator.Implies, Grp(b));
    private static Formula Bin(Formula a, FormulaBinaryOperator op, Formula b) => new Formula.Binary(Grp(a), op, Grp(b));
    private static Formula Plus(Formula a, Formula b) => Bin(a, FormulaBinaryOperator.Add, b);
    private static Formula Times(Formula a, Formula b) => Bin(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Word(Formula n) => Call("Word", n);
    private static Formula Sum(string x, Formula t, Formula body) => Seq(F.Sum, Underscore, Grp(F.Id(x), Sp, InMacro, Sp, t), Sp, body);
    private static Formula OddLength(Formula m) => Plus(Times(D(2), m), D(1));

    private static Formula InverseFormula()
    {
        Formula m = F.Id("m"), x = F.Id("x"), y = F.Id("y"), w = Word(OddLength(m));
        return Disp(All("m", Named("Nat"),
            And(All("x", w, Eq(Call("inverse", m, Call("chi", x)), x)),
                All("y", w, Eq(Call("chi", Call("inverse", m, y)), y)))));
    }
    private static Formula InversionFormula()
    {
        Formula n = F.Id("n"), f = F.Id("f"), y = F.Id("y"), a = F.Id("a"), w = Word(n);
        return Disp(All("n", Named("Nat"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
            All("f", Arrow(w, Call("ZMod", D(2))), All("y", w,
                Eq(Sum("a", w, Times(Call("walsh", f, a), Call("sign", Call("dot", a, y)))),
                    Times(Call("card", w), Call("sign", Call("f", y)))))))));
    }
    private static Formula NonemptyFormula()
    {
        Formula n = F.Id("n"), w = Word(n);
        return Disp(All("n", Named("Nat"), Imp(Rel(D(0), FormulaRelationOperator.LessThan, n),
            All("f", Arrow(w, Call("ZMod", D(2))), Some("a", w,
                Rel(Call("walsh", F.Id("f"), F.Id("a")), FormulaRelationOperator.NotEqual, D(0)))))));
    }
    private static Formula PhaseNonemptyFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), a = F.Id("a"), x = F.Id("x"), w = Word(OddLength(m));
        return Disp(All("m", Named("Nat"), All("b", w, Some("a", w,
            Rel(Sum("x", w, Call("sign", Plus(Call("dot", b, x), Call("dot", a, Call("chi", x))))),
                FormulaRelationOperator.NotEqual, D(0))))));
    }
    private static Formula PhaseFormula()
    {
        Formula m = F.Id("m"), b = F.Id("b"), a = F.Id("a"), x = F.Id("x"), w = Word(OddLength(m));
        return Disp(All("m", Named("Nat"), All("b", w, All("a", w,
            Eq(Sum("x", w, Call("sign", Plus(Call("dot", b, x), Call("dot", a, Call("chi", x))))),
                Call("walsh", Call("inverseComponent", m, b), a))))));
    }
}
