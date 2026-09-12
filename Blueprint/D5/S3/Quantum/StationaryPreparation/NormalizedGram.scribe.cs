using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class NormalizedGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula r = Id("r"), s = Id("s"), w = Id("w"), a = Id("a"), f = Id("f");
        Formula d = Call("normalizationDiagonal", a), g = Call("normalizedGram", a, Id("blank"), Id("U"), Id("x"));
        Formula b = Call("occupationGram", a, Id("blank"), Id("U"), Id("x"));
        Formula legalPair = And(Leq(r, a), Leq(s, a));
        Formula scaleEntry = Setup(All("r", Occupation, All("s", Occupation,
            Imp(And(legalPair, Leq(s, r)), Eq(Inner(RhoAt(r), RhoAt(s)),
                Mul(CastNComplex(M(s)), Inner(RhoAt(Sub(r, s)), f)))))));
        Formula shortZero = Setup(All("r", Occupation, All("s", Occupation,
            Imp(And(And(legalPair, Leq(Card(s), Card(r))), Not(Leq(s, r))),
                Eq(Inner(RhoAt(r), RhoAt(s)), D(0))))));
        Formula comparable = Setup(All("r", Occupation, All("s", Occupation,
            Imp(And(And(legalPair, Leq(s, r)), Unit(f)), Eq(Inner(PhiAt(r), PhiAt(s)),
                Mul(Coefficient(r, s), Moment(Sub(r, s))))))));
        Formula reverse = Setup(All("r", Occupation, All("s", Occupation,
            Imp(And(And(legalPair, Leq(r, s)), Unit(f)), Eq(Inner(PhiAt(r), PhiAt(s)),
                Mul(Coefficient(s, r), Call("star", Moment(Sub(s, r)))))))));
        Formula incomparable = Setup(All("r", Occupation, All("s", Occupation,
            Imp(And(And(And(legalPair, Not(Leq(s, r))), Not(Leq(r, s))), Unit(f)),
                Eq(Inner(PhiAt(r), PhiAt(s)), D(0))))));
        Formula residualPrefix = Setup(All("r", Occupation, Imp(Leq(r, a),
            All("w", Call("List", Id("A")), Imp(Leq(Call("length", w), Card(r)),
                Eq(Call("prefixMemory", Id("blank"), Id("U"), w, RhoAt(r)),
                    Call("ite", Leq(Call("toMultiset", w), r),
                        RhoAt(Sub(r, Call("toMultiset", w))), D(0))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Actual stationary residuals give the full normalized source Gram entries and rank interface.",
            H("Normalized Stationary Gram"), Blocks(
                Paragraph(Text(
                    "A and K are finite types, A has decidable equality, blank belongs to A, " +
                    "and Space(K) is complex Euclidean memory. Unitary(A times K) denotes the " +
                    "complex linear isometric automorphisms of the joint alphabet-memory space. " +
                    "Every occurrence of the schedule below is the constant function with value U. " +
                    "The common-final-memory equation ranges over every word and every memory coordinate.")),
                Paragraph(Text(
                    "residualMemory, prefixMemory, boxOccupation, and occupationGram are the " +
                    "actual PhysicalGram objects. normalizedResidual, residualScale, and " +
                    "sourceMoment are defined in NormalizedResiduals: the scale is sqrt(M(r)), " +
                    "the normalized vector is its complex inverse times residualMemory, and the " +
                    "moment is inner(Complex,normalizedResidual(r),f). Here M(r) means the existing " +
                    "multiplicity(r.card,r), the number of words of that occupation. The inner " +
                    "product conjugates its first operand; star is complex conjugation. NatToReal, " +
                    "NatToComplex, and ofReal are the indicated canonical scalar embeddings.")),
                Theorem("residual_prefix", residualPrefix,
                    "Append every suffix of the remaining length. The existing exact suffix " +
                    "output and injectivity identify the residual when the prefix occupation fits; " +
                    "otherwise every completed word has the wrong occupation and the prefix vector is zero."),
                Theorem("residual_inner_of_le", scaleEntry,
                    "Expand the actual inner product over suffixes of length s.card. Exactly " +
                    "multiplicity(s.card,s) suffixes survive on the second residual, and each " +
                    "leaves the first residual at r minus s. This includes s equal to zero and r equal to s."),
                Theorem("residual_inner_of_not_le", shortZero,
                    "If the shorter occupation does not fit inside the longer one, every potentially " +
                    "surviving suffix on the second residual gives zero on the first."),
                Theorem("normalized_inner_of_le", comparable,
                    "Divide the scaled comparable entry by the two positive normalization factors. " +
                    "The remaining source moment keeps the normalized residual in its first operand."),
                Theorem("normalized_inner_of_ge", reverse,
                    "Conjugate symmetry gives the reverse comparable entry. The positive real " +
                    "coefficient is unchanged and the source moment is conjugated."),
                Theorem("normalized_inner_incomparable", incomparable,
                    "Compare the two total lengths and apply the shorter incompatible-occupation " +
                    "identity, conjugating if necessary. The occupations need not have equal length."),
                Paragraph(Text(
                    "TailBox(a.count) is the dependent product of Fin(a.count(i)+1) over i in A. " +
                    "boxOccupation(a,r) has counts equal to these coordinate values, so it is legal " +
                    "even when some or all capacities vanish. The following matrices are indexed " +
                    "by this same TailBox on both sides and have complex entries. Matrix.gram uses " +
                    "inner(Complex,v(r),v(s)); Matrix.diagonal has the displayed values on its diagonal and zeros elsewhere.")),
                Theorem("normalizedGram", Context(Eq(g,
                    Call("gram", Id("Complex"), LambdaAt("r", Box, PhiAt(BoxOccupation(r)))))),
                    "normalizedGram is the Gram matrix of the actual normalized residual vectors on the existing box."),
                Theorem("normalizationDiagonal", BoxContext(Eq(d,
                    Call("diagonal", LambdaAt("r", Box, CastC(Scale(BoxOccupation(r))))))),
                    "normalizationDiagonal is the complex matrix with positive real sqrt(M(boxOccupation(a,r))) diagonal entries."),
                Theorem("diagonal_positive", BoxContext(All("r", Box,
                    Lt(D(0), Call("re", At(d, r, r))))),
                    "Every real diagonal entry is strictly positive, including the zero-occupation coordinate."),
                Theorem("diagonal_ne_zero", BoxContext(All("r", Box, Ne(At(d, r, r), D(0)))),
                    "Each complex diagonal entry is nonzero."),
                Theorem("diagonal_det_ne_zero", BoxContext(Ne(Call("det", d), D(0))),
                    "The determinant is the product of the nonzero diagonal entries."),
                Theorem("occupation_gram_eq_diagonal", Context(Eq(b, Mul(Mul(d, g), d))),
                    "Scale both actual normalized vectors back to their residual vectors. The " +
                    "left scale is conjugated by the inner product, but equals its conjugate " +
                    "because it is real. This gives exactly B equals D G D."),
                Theorem("occupation_gram_rank_eq", Context(Eq(Call("rank", b), Call("rank", g))),
                    "Left and right multiplication by the invertible diagonal preserves the matrix rank."),
                Theorem("normalized_gram_psd", Context(Call("PosSemidef", g)),
                    "A complex Gram matrix is positive semidefinite."),
                Theorem("normalized_gram_rank_le", Context(Leq(Call("rank", g), Call("FintypeCard", Id("K")))),
                    "The existing rank bound for the actual occupationGram transfers through the diagonal rank equality."))));
    }

    private static Formula Setup(Formula body) => Context(All("f", Space, Imp(Output(), body)));
    private static Formula Context(Formula body) => Types(All("a", Occupation,
        All("blank", Id("A"), All("U", Unitary, All("x", Space, body)))));
    private static Formula Types(Formula body) => All("A", Id("Type"), All("K", Id("Type"),
        Imp(And(And(Call("Fintype", Id("A")), Call("Fintype", Id("K"))),
            Call("DecidableEq", Id("A"))), body)));
    private static Formula BoxContext(Formula body) => All("A", Id("Type"),
        Imp(And(Call("Fintype", Id("A")), Call("DecidableEq", Id("A"))), All("a", Occupation, body)));
    private static Formula Output() => All("w", Arrow(Call("Fin", Card(Id("a"))), Id("A")),
        All("k", Id("K"), Eq(Call("circuit", LambdaAt("t", N, Id("U")), Card(Id("a")), D(0),
            Call("initialized", Id("blank"), Card(Id("a")), Id("x")), Call("pair", Id("w"), Id("k"))),
            Mul(Call("sectorVector", Card(Id("a")), Id("a"), Id("w")), At(Id("f"), Id("k"))))));
    private static Formula Coefficient(Formula r, Formula s) => CastC(SqrtAt(
        Div(Mul(CastR(M(s)), CastR(M(Sub(r, s)))), CastR(M(r)))));
    private static Formula RhoAt(Formula r) => Call("residualMemory", Id("a"), Id("blank"), Id("U"), Id("x"), r);
    private static Formula PhiAt(Formula r) => Call("normalizedResidual", Id("a"), Id("blank"), Id("U"), Id("x"), r);
    private static Formula Moment(Formula r) => Call("sourceMoment", Id("a"), Id("blank"), Id("U"), Id("x"), Id("f"), r);
    private static Formula Scale(Formula r) => Call("residualScale", r);
    private static Formula M(Formula r) => Call("multiplicity", Card(r), r);
    private static Formula Card(Formula r) => Call("card", r);
    private static Formula Inner(Formula x, Formula y) => Call("inner", Id("Complex"), x, y);
    private static Formula BoxOccupation(Formula r) => Call("boxOccupation", Id("a"), r);
    private static Formula Box => Call("TailBox", LambdaAt("i", Id("A"), Call("count", Id("a"), Id("i"))));
    private static Formula CastR(Formula n) => Call("NatToReal", n);
    private static Formula CastNComplex(Formula n) => Call("NatToComplex", n);
    private static Formula CastC(Formula r) => Call("ofReal", r);
    private static Formula SqrtAt(Formula r) => Seq(Sqrt, Grp(r));
    private static Formula Unit(Formula x) => Eq(Call("norm", x), D(1));
    private static Formula Space => Call("Space", Id("K"));
    private static Formula Unitary => Call("Unitary", Call("Product", Id("A"), Id("K")));
    private static Formula Occupation => Call("Multiset", Id("A"));
    private static Formula N => Seq(Mathbb, Grp(Id("N")));
    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => At(Id(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Arrow(Formula x, Formula y) => Seq(x, Sp, To, Sp, y);
    private static Formula LambdaAt(string name, Formula domain, Formula body) => Seq(Id(name), Colon, domain, Sp, Mapsto, Sp, body);
    private static Formula All(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Not(Formula x) => Seq(Neg, Sp, Grp(x));
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Ne(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.NotEqual, y);
    private static Formula Leq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Div(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static DocumentBlock Theorem(string name, Formula formula, string text) => Describe.Lean(
        DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(
            "D5/S3/Quantum/StationaryPreparation/NormalizedGram." + name), H(name),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))));
}
