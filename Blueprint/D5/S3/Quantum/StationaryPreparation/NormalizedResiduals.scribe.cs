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
                    "For a nonzero remaining occupation, an absent symbol has zero image. No emission rule is imposed at the terminal residual."),
                PhysicalCompanions())));
    }


    private static DocumentBlock PhysicalCompanions()
    {
        Formula a = Id("a"), r = Id("r"), i = Id("i"), u = Id("u"), k = Id("k");
        Formula erased = Call("erase", r, i), single = Call("singleton", Head);
        Formula step = All("r", Occupation, Imp(And(Leq(r, a), Ne(r, D(0))),
            All("i", Id("A"), All("k", PhysicalK, Eq(
                At(At(Gate, Call("blankMemory", Head, PhysicalRho(r))), Call("pair", i, k)),
                Call("ite", Mem(i, r), At(PhysicalRho(erased), k), D(0)))))));
        return new DocumentBlock.Section(H("Identification with the concrete padding circuit"), Blocks(
            Paragraph(Text(
                "In this section A is finite and nonempty with decidable equality, and a is any multiset on A. " +
                "The head is maximalHead(a), whose capacity is the maximum of a.count. The actual memory " +
                "index is Fin(proposedDimension(a)); proposedDimension is the product of (a.count(i)+1) " +
                "minus the maximum count. physicalResidual(a,r) is C's existing paddingResidual embedded " +
                "by physicalMemoryEquiv(a), physicalGate(a) is C's fixed unitary, and physicalFinal(a) " +
                "is its sink basis vector of norm one. These are the existing concrete vectors and gate.")),
            Paragraph(Text(
                "physicalInitial(a) names exactly the inverse sqrt(M(a)) times physicalResidual(a,a) " +
                "already used by C's output theorem. The formulas below use no output or vector-identity " +
                "hypothesis. The output is proved from C's positive-tail, absent-letter and tail-free " +
                "steps. The identification compares actual suffix outputs and uses the existing " +
                "isometric suffix injectivity, so it fixes phase as well as norm.")),
            Theorem("physicalInitial", PhysicalContext(Eq(Initial, PhysicalScaled(a))),
                "This is a vector in the same Space(Fin(proposedDimension(a))); no second normalized family is defined."),
            Theorem("physical_residual_step", PhysicalContext(step),
                "Assemble the already-proved step branches for every legal nonterminal residual."),
            Theorem("physical_initial_output", PhysicalContext(PhysicalOutput()),
                "C's genuine all-word circuit output supplies the physical hypothesis used by B's residual theory."),
            Theorem("physical_scaled_initial", PhysicalContext(Eq(
                Call("scaledInitial", a, Initial), PhysicalRho(a))),
                "The positive scale cancels its inverse, including the all-zero occupation."),
            Theorem("physical_residual_identification", PhysicalLegal(Eq(
                Call("residualMemory", a, Head, Gate, Initial, r), PhysicalRho(r))),
                "B's prefix-derived residual is exactly C's chosen physicalResidual for every r less than or equal to a."),
            Theorem("physical_normalized_identification", PhysicalLegal(Eq(PhysicalPhi(r), PhysicalScaled(r))),
                "The existing B normalizedResidual at these concrete parameters equals the scalar-normalized C vector."),
            Theorem("physical_prefix_identification", PhysicalPrefix(Eq(
                Call("prefixMemory", Head, Gate, u, PhysicalRho(a)), PhysicalRho(r))),
                "Every ordered prefix of occupation a minus r has the same actual residual, with the unscaled C initial."),
            Theorem("physical_prefix_normalized", PhysicalPrefix(Eq(
                Call("prefixMemory", Head, Gate, u, Initial),
                Smul(CastC(SqrtAt(Div(CastR(M(r)), CastR(M(a))))), PhysicalScaled(r)))),
                "For the unit initial, the exact prefix multiplier is sqrt(M(r)/M(a)), embedded in the complex numbers."),
            Theorem("physical_normalized_norm", PhysicalLegal(Unit(PhysicalScaled(r))),
                "Identification transfers B's norm theorem using the proved output and C's unit final memory."),
            Theorem("physical_initial_norm", PhysicalContext(Unit(Initial)),
                "Specialize the preceding actual-vector norm at r equal to a."),
            Theorem("physical_normalized_zero", PhysicalContext(Eq(PhysicalPhi(D(0)), Final)),
                "The terminal scale is one and the identified terminal residual is exactly the common final memory."),
            Theorem("physical_head_singleton_le", PhysicalContext(Imp(PositiveMaximum, Leq(single, a))),
                "Positive maximum capacity implies head membership via maximal_head_spec; it is not assumed."),
            Theorem("physical_normalized_head", PhysicalContext(Imp(PositiveMaximum,
                Eq(PhysicalPhi(D(0)), PhysicalPhi(single)))),
                "The legal head singleton has zero tail and multiplicity one. Both normalized vectors equal physicalFinal(a)."),
            Theorem("physical_normalized_letter", PhysicalContext(All("r", Occupation,
                Imp(And(Leq(r, a), Ne(r, D(0))), All("i", Id("A"), Eq(
                    Call("letter", Head, Gate, i, PhysicalScaled(r)),
                    Call("ite", Mem(i, r), Smul(CastC(SqrtAt(
                        Div(CastR(Call("count", r, i)), CastR(Card(r))))), PhysicalScaled(erased)), D(0))))))),
                "Rewrite the identified actual family and directly reuse B's existing square-root coefficient and absent-letter theorems."),
            Paragraph(Text(
                "All statements retain zero and mixed capacities. The all-zero initial equals the unit final vector " +
                "in C's existing dimension-one branch. The emission equation requires r nonzero; the head-singleton " +
                "equation requires positive maximum capacity. NormalizedGram uses this exact identified family " +
                "to prove full generated span and positive-maximum nonterminal span in the physical memory."))));
    }

    private static Formula PhysicalContext(Formula body) => All("A", Id("Type"),
        Imp(And(Call("Fintype", Id("A")), And(Call("DecidableEq", Id("A")), Call("Nonempty", Id("A")))),
            All("a", Occupation, body)));
    private static Formula PhysicalLegal(Formula body) => PhysicalContext(All("r", Occupation,
        Imp(Leq(Id("r"), Id("a")), body)));
    private static Formula PhysicalPrefix(Formula body) => PhysicalLegal(All("u", Call("List", Id("A")),
        Imp(Eq(Call("toMultiset", Id("u")), Sub(Id("a"), Id("r"))), body)));
    private static Formula PhysicalOutput() => All("w", Arrow(Call("Fin", Card(Id("a"))), Id("A")),
        All("k", PhysicalK, Eq(Call("circuit", LambdaAt("t", N, Gate), Card(Id("a")), D(0),
            Call("initialized", Head, Card(Id("a")), Initial), Call("pair", Id("w"), Id("k"))),
            Mul(Call("sectorVector", Card(Id("a")), Id("a"), Id("w")), At(Final, Id("k"))))));
    private static Formula Head => Call("maximalHead", Id("a"));
    private static Formula Gate => Call("physicalGate", Id("a"));
    private static Formula Initial => Call("physicalInitial", Id("a"));
    private static Formula Final => Call("physicalFinal", Id("a"));
    private static Formula PhysicalK => Call("Fin", Call("proposedDimension", Id("a")));
    private static Formula PositiveMaximum => Lt(D(0), Call("sup", Id("univ"), Call("count", Id("a"))));
    private static Formula PhysicalRho(Formula r) => Call("physicalResidual", Id("a"), r);
    private static Formula PhysicalPhi(Formula r) => Call("normalizedResidual", Id("a"), Head, Gate, Initial, r);
    private static Formula PhysicalScaled(Formula r) => Smul(Call("inv", CastC(Scale(r))), PhysicalRho(r));

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
