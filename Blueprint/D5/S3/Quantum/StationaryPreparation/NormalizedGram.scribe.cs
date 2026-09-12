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
                    "The existing rank bound for the actual occupationGram transfers through the diagonal rank equality."),
                PhysicalCompanions())));
    }


    private static DocumentBlock PhysicalCompanions()
    {
        Formula r = Id("r"), x = Id("x");
        Formula positive = Lt(D(0), Call("sup", Id("univ"), Call("count", Id("a"))));
        Formula left = PhysicalCombination(false), right = PhysicalCombination(true);
        return new DocumentBlock.Section(H("The actual normalized fixed tensor isometry"), Blocks(
            Paragraph(Text(
                "Here A is finite and nonempty with decidable equality and a is any occupation multiset. " +
                "K is exactly Fin(proposedDimension(a)), head is maximalHead(a), U is physicalGate(a), " +
                "and x is physicalInitial(a) as identified in NormalizedResiduals. Every phi below is " +
                "inverse sqrt(M(r)) times C's actual physicalResidual(a,r), proved exactly equal to the " +
                "existing normalizedResidual(a,head,U,x,r). The output and unit final vector are proved for these data.")),
            Paragraph(Text(
                "The orthonormal tensor basis uses the alphabet factor first and the same memory factor second. " +
                "R is the repr equivalence of tensorProduct(basisFun(A,Complex),basisFun(K,Complex)); " +
                "it sends a pure tensor z tensor y to the joint coordinate (i,k) equal to y(k) times z(i). " +
                "basis(i) is the alphabet coordinate basis. tmul(Complex,z,y) denotes this ordered complex " +
                "tensor product, smul is complex scalar multiplication, and comp means composition with " +
                "the rightmost map applied first. No additional circuit or normalized family is constructed.")),
            Theorem("physicalTensorEmission", PhysicalContext(Eq(PhysicalV,
                Call("comp", Call("toLinearIsometry", Call("symm", PhysicalRepr)), PhysicalEmission))),
                "This is a complex linear isometry from Space(K) to Space(A) tensor Space(K), obtained from the actual blank-input emission."),
            Theorem("physical_tensor_coordinates", PhysicalContext(All("x", PhysicalSpace,
                Eq(At(PhysicalRepr, At(PhysicalV, x)), At(PhysicalEmission, x)))),
                "The exact coordinate equivalence identifies the tensor map with PhysicalGram.emission for C's fixed gate and blank."),
            Theorem("physical_tensor_emission", PhysicalContext(All("r", Occupation,
                Imp(And(Leq(r, Id("a")), Ne(r, D(0))), Eq(At(PhysicalV, PhysicalPhi(r)), PhysicalSum(r))))),
                "For each legal nonterminal residual, the actual map has the source's sqrt(count/card) tensor expansion. " +
                "The scalar is embedded from the reals into the complex numbers. Absent symbols have count zero " +
                "and therefore contribute zero, while the erased residual stays legal."),
            Theorem("physical_emission_linearCombination", PhysicalFinite(
                Eq(At(PhysicalV, left), right)),
                "For any index type I, any family r(j) of legal nonzero residuals, and any finitely supported " +
                "complex coefficients c, applying the same isometry commutes with the finite linear combination " +
                "and substitutes the displayed normalized tensor expansion."),
            Theorem("physical_image_dependency_iff", PhysicalAllFinite(
                new Formula.Logic(Eq(left, D(0)), FormulaLogicOperator.Iff,
                    Eq(PhysicalImageCombination(), D(0)))),
                "The actual isometry preserves all finite dependencies of the total concrete vector family, " +
                "including terminal zero occupation. This image statement has no nonterminal restriction; " +
                "identification with B applies on the legal box. The following source expansion retains its own domain."),
            Theorem("physical_dependency_iff", PhysicalFinite(
                new Formula.Logic(Eq(left, D(0)), FormulaLogicOperator.Iff, Eq(right, D(0)))),
                "Injectivity and linearity give both directions: every finite dependency of this actual family " +
                "is exactly a dependency of its prescribed emission images. This is not restricted to a conditional kernel recurrence."),
            Theorem("physical_nonterminal_span_eq", PhysicalContext(Imp(positive,
                Eq(PhysicalSpan(true), PhysicalSpan(false)))),
                "The actual normalized terminal vector equals the legal nonzero head-singleton vector when " +
                "the maximum capacity is positive. Removing the terminal index therefore preserves the generated subspace."),
            Theorem("physical_generated_span_top", PhysicalContext(Eq(PhysicalSpan(false), Id("top"))),
                "Put the actual legal normalized vectors in their own generated subspace S. Their Gram equals " +
                "the actual normalizedGram by the proved C/B identification. The existing stationary Gram lower " +
                "bound and diagonal rank equality give proposedDimension(a) at most its rank. Coordinates in an " +
                "orthonormal basis of S bound that rank by dim(S), so S is the whole physical memory."),
            Theorem("physical_nonterminal_span_top", PhysicalContext(Imp(positive,
                Eq(PhysicalSpan(true), Id("top")))),
                "Full generation and the terminal/head-singleton equality prove that the nonterminal vectors " +
                "span the actual memory whenever the maximum capacity is positive."),
            Paragraph(Text(
                "linearCombination(Complex,v,c) means the finite sum of c(j) times v(j); Finsupp(I,Complex) " +
                "is its finitely supported coefficient type. The displayed sets are setOf predicates over the same " +
                "Space(K), span is the complex linear span, and top is the whole physical memory subspace. " +
                "Zero and mixed capacities remain allowed. The all-zero dimension-one branch is separate; " +
                "no nonterminal span assertion is made there. Actual padding moments, block factorization, block " +
                "and aggregate ranks remain separate source obligations."))));
    }

    private static Formula PhysicalContext(Formula body) => All("A", Id("Type"),
        Imp(And(Call("Fintype", Id("A")), And(Call("DecidableEq", Id("A")), Call("Nonempty", Id("A")))),
            All("a", Occupation, body)));
    private static Formula PhysicalAllFinite(Formula body) => PhysicalContext(All("I", Id("Type"),
        All("r", Arrow(Id("I"), Occupation),
            All("c", Call("Finsupp", Id("I"), Id("Complex")), body))));
    private static Formula PhysicalImageCombination() => Call("linearCombination", Id("Complex"),
        LambdaAt("j", Id("I"), At(PhysicalV, PhysicalPhi(At(Id("r"), Id("j"))))), Id("c"));
    private static Formula PhysicalFinite(Formula body) => PhysicalContext(All("I", Id("Type"),
        All("r", Arrow(Id("I"), Occupation), Imp(All("j", Id("I"),
            And(Leq(At(Id("r"), Id("j")), Id("a")), Ne(At(Id("r"), Id("j")), D(0)))),
            All("c", Call("Finsupp", Id("I"), Id("Complex")), body)))));
    private static Formula PhysicalCombination(bool images) => Call("linearCombination", Id("Complex"),
        LambdaAt("j", Id("I"), images ? PhysicalSum(At(Id("r"), Id("j"))) :
            PhysicalPhi(At(Id("r"), Id("j")))), Id("c"));
    private static Formula PhysicalSpan(bool nonterminal)
    {
        Formula r = Id("r");
        Formula belongs = And(Leq(r, Id("a")), nonterminal ?
            And(Ne(r, D(0)), Eq(PhysicalPhi(r), Id("v"))) : Eq(PhysicalPhi(r), Id("v")));
        return Call("span", Id("Complex"), Call("setOf", LambdaAt("v", PhysicalSpace,
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("r"), Occupation, belongs))));
    }
    private static Formula PhysicalSum(Formula r) => SumAt("i", Id("A"),
        Call("smul", CastC(SqrtAt(Div(CastR(Call("count", r, Id("i"))), CastR(Card(r))))),
            Call("tmul", Id("Complex"), Call("basis", Id("i")), PhysicalPhi(Call("erase", r, Id("i"))))));
    private static Formula PhysicalPhi(Formula r) => Call("smul", Call("inv", CastC(Scale(r))),
        Call("physicalResidual", Id("a"), r));
    private static Formula PhysicalK => Call("Fin", Call("proposedDimension", Id("a")));
    private static Formula PhysicalSpace => Call("Space", PhysicalK);
    private static Formula PhysicalV => Call("physicalTensorEmission", Id("a"));
    private static Formula PhysicalEmission => Call("emission", Call("maximalHead", Id("a")), Call("physicalGate", Id("a")));
    private static Formula PhysicalRepr => Call("repr", Call("tensorProduct",
        Call("basisFun", Id("A"), Id("Complex")), Call("basisFun", PhysicalK, Id("Complex"))));
    private static Formula SumAt(string name, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(Id(name), Colon, domain)), Grp(body));

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
