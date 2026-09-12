using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.StationaryPreparation;

internal sealed class NormalizedResidualsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula r = Id("r"), i = Id("i"), u = Id("u"), n = Id("n"), w = Id("w");
        Formula x = Id("x"), y = Id("y"), f = Id("f"), a = Id("a");
        Formula phi = PhiAt(r), rho = RhoAt(r), erased = Call("erase", r, i);
        Formula prefixInner = Types(All("blank", Id("A"), All("U", Unitary,
            All("n", N, All("x", Space, All("y", Space,
                Eq(Inner(x, y), SumAt("w", Arrow(Call("Fin", n), Id("A")),
                    Inner(Prefix(Call("ListOfFn", w), x), Prefix(Call("ListOfFn", w), y))))))))));
        Formula legalStep = Setup(All("r", Occupation, Imp(And(Leq(r, a), Ne(r, D(0))),
            All("i", Id("A"), Imp(Mem(i, r),
                Eq(Letter(i, phi), Smul(CastC(SqrtAt(Div(CastR(Call("count", r, i)),
                    CastR(Card(r))))), PhiAt(erased))))))));
        Formula absentStep = Setup(All("r", Occupation, Imp(And(Leq(r, a), Ne(r, D(0))),
            All("i", Id("A"), Imp(Not(Mem(i, r)), Eq(Letter(i, phi), D(0)))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Actual normalized residual memories obey the stationary source amplitudes.",
            H("Normalized Stationary Residuals"), Blocks(
                Paragraph(Text(
                    "A and K are finite types, A has decidable equality, and blank is a symbol of A. " +
                    "Space(K) is the complex Euclidean space on K. Unitary(A times K) is its " +
                    "complex linear isometric automorphism type on the joint alphabet-memory space. " +
                    "The same U acts at every circuit step. The output hypothesis below quantifies " +
                    "every word and memory coordinate, with one common final vector f.")),
                Paragraph(Text(
                    "multiplicity(n,r), occupation, and sectorVector are the objects of " +
                    "OccupancyWordSectors. multiplicity counts length-n words of occupation r. " +
                    "sectorVector(n,r) is its inverse-square-root coefficient on these words and " +
                    "zero otherwise. residualMemory, prefixMemory, and letter are the actual " +
                    "PhysicalGram objects: the residual uses a representative prefix of occupation " +
                    "a minus r applied to sqrt(multiplicity(a.card,a)) times x. ListOfFn enumerates " +
                    "a finite word in order. NatToReal and NatToComplex are the canonical natural " +
                    "casts; ofReal embeds a real number into the complex numbers. smul denotes " +
                    "complex scalar multiplication. The inner product is conjugate-linear in " +
                    "its first operand.")),
                Theorem("residualScale", CountContext(All("r", Occupation,
                    Eq(Scale(r), SqrtAt(CastR(M(r)))))),
                    "residualScale(r) is a real number: the positive square root of the word multiplicity."),
                Theorem("normalizedResidual", Context(All("r", Occupation,
                    Eq(phi, Smul(Call("inv", CastC(Scale(r))), rho)))),
                    "normalizedResidual(a,blank,U,x,r) lies in Space(K) and is the actual residual divided by its real scale."),
                Theorem("sourceMoment", Context(All("f", Space, All("r", Occupation,
                    Eq(Moment(r), Inner(phi, f))))),
                    "sourceMoment(a,blank,U,x,f,r) is complex. Its first inner-product operand is the normalized residual."),
                Theorem("multiplicity_ne_zero", CountContext(All("r", Occupation, Ne(M(r), D(0)))),
                    "The existing positive word count makes every normalization denominator nonzero, including r equal to zero."),
                Theorem("scale_pos", CountContext(All("r", Occupation, Lt(D(0), Scale(r)))),
                    "Positive multiplicity has a strictly positive real square root."),
                Theorem("scale_ne_zero", CountContext(All("r", Occupation, Ne(CastC(Scale(r)), D(0)))),
                    "The positive real scale remains nonzero after embedding into the complex numbers."),
                Theorem("scale_sq", CountContext(All("r", Occupation, Eq(Sq(Scale(r)), CastR(M(r))))),
                    "Squaring the scale recovers the word count."),
                Theorem("scale_zero", CountContext(Eq(Scale(D(0)), D(1))),
                    "The empty word is the single word of zero occupation, so its scale is one."),
                Theorem("scale_normalized", Context(All("r", Occupation,
                    Eq(Smul(CastC(Scale(r)), phi), rho))),
                    "Multiplying the normalized vector by its scale recovers the same actual residual."),
                Theorem("prefix_inner_sum", prefixInner,
                    "Initialize an n-letter blank register and apply the fixed-unitary circuit. " +
                    "Both maps are isometries. Expanding their inner product in all word and " +
                    "memory coordinates gives this sum of actual prefix-memory inner products."),
                Theorem("residual_inner_self", Legal(r, Eq(Inner(rho, rho), CastNComplex(M(r))), true),
                    "Each complete suffix of occupation r produces f; every other suffix of that " +
                    "length produces zero. The all-word inner-product sum therefore counts exactly multiplicity(r.card,r)."),
                Theorem("residual_norm_sq", Legal(r, Eq(Sq(Call("norm", rho)), CastR(M(r))), true),
                    "Taking the real part of the residual inner-self identity gives its squared norm."),
                Theorem("normalized_norm", Legal(r, Eq(Call("norm", phi), D(1)), true),
                    "The residual norm equals its positive real scale; division yields a unit vector for every legal r."),
                Theorem("normalized_zero", Setup(Eq(PhiAt(D(0)), f)),
                    "The normalized terminal residual is exactly the common final memory, including phase."),
                Theorem("normalized_initial", Context(Eq(PhiAt(a), x)),
                    "At remaining occupation a the representative prefix is empty; normalization recovers x."),
                Theorem("source_moment_zero", Setup(Imp(Unit(f), Eq(Moment(D(0)), D(1)))),
                    "The final memory has unit norm, so its inner product with itself is one."),
                Theorem("prefix_normalized", Setup(All("r", Occupation, Imp(Leq(r, a),
                    All("u", Call("List", Id("A")), Imp(Eq(Call("toMultiset", u), Sub(a, r)),
                        Eq(Prefix(u, x), Smul(CastC(SqrtAt(Div(CastR(M(r)), CastR(M(a))))), phi))))))),
                    "Representative independence identifies every actual legal prefix. Removing " +
                    "the initial scale gives the square root of the ratio of the remaining and total multiplicities."),
                Theorem("normalized_letter_of_mem", legalStep,
                    "For a nonzero remaining occupation, the existing legal residual transition " +
                    "and multiplicity erase identity give sqrt(count(i)/card(r)) times the erased normalized residual."),
                Theorem("normalized_letter_of_not_mem", absentStep,
                    "For a nonzero remaining occupation, an absent symbol has zero image. No emission rule is imposed at the terminal residual."))));
    }

    private static Formula Legal(Formula r, Formula body, bool unit) => Setup(All("r", Occupation,
        Imp(unit ? And(Leq(r, Id("a")), Unit(Id("f"))) : Leq(r, Id("a")), body)));
    private static Formula Setup(Formula body) => Context(All("f", Space, Imp(Output(), body)));
    private static Formula Context(Formula body) => Types(All("a", Occupation,
        All("blank", Id("A"), All("U", Unitary, All("x", Space, body)))));
    private static Formula Types(Formula body) => All("A", Id("Type"), All("K", Id("Type"),
        Imp(And(And(Call("Fintype", Id("A")), Call("Fintype", Id("K"))),
            Call("DecidableEq", Id("A"))), body)));
    private static Formula CountContext(Formula body) => All("A", Id("Type"),
        Imp(And(Call("Fintype", Id("A")), Call("DecidableEq", Id("A"))), body));
    private static Formula Output() => All("w", Arrow(Call("Fin", Card(Id("a"))), Id("A")),
        All("k", Id("K"), Eq(Call("circuit", LambdaAt("t", N, Id("U")), Card(Id("a")), D(0),
            Call("initialized", Id("blank"), Card(Id("a")), Id("x")), Call("pair", Id("w"), Id("k"))),
            Mul(Call("sectorVector", Card(Id("a")), Id("a"), Id("w")), At(Id("f"), Id("k"))))));
    private static Formula Prefix(Formula word, Formula x) => Call("prefixMemory", Id("blank"), Id("U"), word, x);
    private static Formula Letter(Formula i, Formula x) => Call("letter", Id("blank"), Id("U"), i, x);
    private static Formula RhoAt(Formula r) => Call("residualMemory", Id("a"), Id("blank"), Id("U"), Id("x"), r);
    private static Formula PhiAt(Formula r) => Call("normalizedResidual", Id("a"), Id("blank"), Id("U"), Id("x"), r);
    private static Formula Moment(Formula r) => Call("sourceMoment", Id("a"), Id("blank"), Id("U"), Id("x"), Id("f"), r);
    private static Formula Scale(Formula r) => Call("residualScale", r);
    private static Formula M(Formula r) => Call("multiplicity", Card(r), r);
    private static Formula Card(Formula r) => Call("card", r);
    private static Formula Inner(Formula x, Formula y) => Call("inner", Id("Complex"), x, y);
    private static Formula Smul(Formula c, Formula x) => Call("smul", c, x);
    private static Formula CastR(Formula n) => Call("NatToReal", n);
    private static Formula CastNComplex(Formula n) => Call("NatToComplex", n);
    private static Formula CastC(Formula r) => Call("ofReal", r);
    private static Formula SqrtAt(Formula r) => Seq(Sqrt, Grp(r));
    private static Formula Sq(Formula r) => new Formula.Power(r, D(2));
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
    private static Formula Mem(Formula x, Formula y) => Seq(x, Sp, InMacro, Sp, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Div(Formula x, Formula y) => Seq(Frac, Grp(x), Grp(y));
    private static Formula SumAt(string name, Formula domain, Formula body) => Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, domain)), Grp(body));
    private static DocumentBlock Theorem(string name, Formula formula, string text) => Describe.Lean(
        DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(
            "D5/S3/Quantum/StationaryPreparation/NormalizedResiduals." + name), H(name),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))));
}
