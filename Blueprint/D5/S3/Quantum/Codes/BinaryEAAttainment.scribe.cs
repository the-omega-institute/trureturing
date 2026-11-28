using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Codes;

internal sealed class BinaryEAAttainmentDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Codes/BinaryEAAttainment.";
    private static readonly Formula N = F.Id("n");
    private static readonly Formula U = F.Id("U");
    private static readonly Formula W = F.Id("W");
    private static readonly Formula I = F.Id("I");
    private static readonly Formula V = F.Id("v");
    private static readonly Formula SiteIndex = F.Id("i");
    private static readonly Formula AddedSite = F.Id("j");
    private static readonly Formula Nat = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula Field = Call("ZMod", D(2));
    private static readonly Formula Universe = Named("univ");
    private static readonly Formula Top = Named("top");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional counts of binary words vanishing on sets of sites control radical projection ranks "
        + "and bound the size of the radical support.",
        H("Coordinate kernels and support for binary Singleton attainment"),
        Blocks(
            Definition("site", "A single coordinate pair",
                AtLength(N, All(SiteIndex, Sites(N), All(V, Words(N),
                    Equal(Site(SiteIndex, V), Pair(Component(V, "fst", SiteIndex), Component(V, "snd", SiteIndex)))))),
                "The two entries are the position and momentum bits at the same site."),
            Definition("restrictSites", "Restriction to a finite set of sites",
                AtLength(N, All(I, SiteSets(N), All(V, Words(N), All(SiteIndex, I,
                    Equal(Apply(Call("restrictSites", I), V, SiteIndex),
                        Site(Seq(SiteIndex, Dot, F.Id("val")), V)))))),
                "The codomain is indexed by the subtype of sites in the prescribed set."),
            Definition("radical", "Radical of the restricted symplectic form",
                AtLength(N, All(U, Spaces(N), Equal(Radical(U), Intersection(U, Orthogonal(N, U))))),
                "The orthogonal complement uses the ambient binary symplectic form."),
            Definition("zeroCount", "Number of zero coordinate pairs",
                AtLength(N, All(V, Words(N),
                    Equal(Zeros(V), Card(Filter(SiteIndex, Equal(Site(SiteIndex, V), D(0))))))),
                "A site contributes exactly when both bits vanish."),
            Definition("Attainment", "Exact binary attainment", Attainment(),
                "Weight counts nonzero coordinate pairs. The universal lower bound and an attaining "
                + "nonradical word together specify the exact minimum."),
            Definition("ZeroBound", "At most three zero sites outside the radical",
                AtLength(N, All(U, Spaces(N),
                    Logic(Call("ZeroBound", U), FormulaLogicOperator.Iff,
                        All(V, Words(N), Nonradical(U, Le(Zeros(V), D(3))))))),
                "Radical words are unrestricted by this predicate."),
            Theorem("zeroBound_of_weight_bound", "Weight lower bound implies the zero-site bound",
                AtLength(N, All(U, Spaces(N),
                    Given(Call("ZeroBound", U), Le(D(6), N), WeightBound()))),
                "The zero count is bounded by the ambient length, so the weight subtraction is exact."),
            Definition("siteKernel", "Subspace vanishing on a site set",
                OverSpaceAndSites(Equal(Kernel(W, I), Intersection(W, Call("ker", Call("restrictSites", I))))),
                "The intersection keeps the kernel in the ambient word space."),
            Definition("kernelCount", "Cardinality of a coordinate kernel",
                OverSpaceAndSites(Equal(Count(W, I), new Formula.Power(D(2), Dim(Kernel(W, I))))),
                "The base is two because the kernel is a binary vector space."),
            Theorem("dim_kernel_add_rank", "Rank and nullity of the restricted site map",
                OverSpaceAndSites(Equal(Add(Dim(Kernel(W, I)), RestrictedRank(W, I)), Dim(W))),
                "The ambient kernel and the kernel with domain restricted to W have equal dimension."),
            Theorem("kernelCount_inequality", "Conditional coordinate-kernel count", KernelInequality(),
                "Each word outside the radical that vanishes on the prescribed set can vanish at "
                + "at most three sites in total. Adding one site decreases the dimension of a kernel by at most two."),
            Theorem("pair_kernel_dim_ge_two", "Two-site radical kernels at length at least nine",
                AtLength(N, PairBound(N, Le(D(2), Dim(Kernel(Radical(U), I))), Le(D(9), N))),
                "The count over extensions of a pair forces at least four radical words in the pair kernel."),
            Theorem("pair_kernel_dim_pos_at_eight", "Positive two-site radical kernel at length eight",
                PairBound(D(8), new Formula.Relation(D(0), FormulaRelationOperator.LessThan, Dim(Kernel(Radical(U), I)))),
                "Each pair shares at least one nonzero radical word that vanishes on it."),
            Theorem("radical_site_rank_le_one", "Radical site rank at length at least nine",
                CodeOfDimensions(All(SiteIndex, Sites(N),
                    Le(RestrictedRank(Radical(U), Seq(OpenBrace, SiteIndex, CloseBrace)), D(1))), Le(D(9), N)),
                "A rank-two site would have the same radical kernel as every pair containing it. The common kernel would then vanish at every site."),
            Definition("support", "Union of occupied sites",
                AtLength(N, All(W, Spaces(N), Equal(Support(W), Filter(SiteIndex, OccupiedSite())))),
                "The support is taken across all words of the subspace."),
            Theorem("mem_support", "Membership in the radical-support construction",
                AtLength(N, All(W, Spaces(N), All(SiteIndex, Sites(N),
                    Logic(Member(SiteIndex, Support(W)), FormulaLogicOperator.Iff, OccupiedSite())))),
                "A single word with a nonzero pair witnesses membership."),
            Definition("supportedOn", "Words supported on a specified site set",
                AtLength(N, All(I, SiteSets(N), Equal(Call("supportedOn", I), Kernel(Top, Complement(I))))),
                "The site kernel is imposed on the complement of the prescribed sites."),
            Definition("mask", "Projection that zeroes sites outside a prescribed set",
                Mask(),
                "The two implications give the coordinate pair of the projected word at every site."),
            Theorem("core_injective", "Injectivity of projection to the radical support",
                AtLength(N, All(U, Spaces(N),
                    Given(Call("Injective", Call("domRestrict", Call("mask", Support(Radical(U))), U)),
                        Call("ZeroBound", U), Le(D(4), Card(Support(Radical(U))))))),
                "A kernel word already vanishes on the radical support. With at least four such sites "
                + "it lies in the radical, where it also vanishes at all other sites."),
            Theorem("core_le_orthogonal", "The projected code is supported and orthogonal to the radical",
                AtLength(N, All(U, Spaces(N),
                    Le(Call("map", Call("mask", Support(Radical(U))), U),
                        Intersection(Orthogonal(N, Radical(U)), Call("supportedOn", Support(Radical(U))))))),
                "Masking outside the radical support preserves the pairing with every radical word."),
            Theorem("seven_le_support", "At least seven radical support sites",
                CodeOfDimensions(Le(D(7), Card(Support(Radical(U))))),
                "At six support sites the masked code fills the supported orthogonal complement. Zero and the eighteen single-site errors would require nineteen distinct four-bit syndromes."),
            Theorem("radical_support_upper_bound", "Upper bounds on the radical support at length at least nine",
                CodeOfDimensions(And(
                    Le(Add(Multiply(D(8), N), Multiply(D(3), Card(Support(Radical(U))))), D(1, 2, 0)),
                    Le(Card(Support(Radical(U))), D(1, 0))), Le(D(9), N)),
                "At length at least nine all occupied radical sites project to lines. "
                + "The one-site conditional count across four independent types gives the joint length and support bound."))));

    private static Formula Sites(Formula length) => Call("Fin", length);
    private static Formula SiteSets(Formula length) => Call("Finset", Sites(length));
    private static Formula Words(Formula length)
    {
        var bits = new Formula.TypeArrow(Sites(length), Field);
        return Paren(Seq(Paren(bits), Sp, Times, Sp, Paren(bits)));
    }

    private static Formula Spaces(Formula length) => Call("Submodule", Field, Words(length));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Paren(Seq(variable, Colon, Sp, type)), Comma, Sp, body);
    private static Formula ExistsIn(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Paren(Seq(variable, Colon, Sp, type)), Comma, Sp, body);
    private static Formula AtLength(Formula length, Formula body) => All(length, Nat, body);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Paren(a), op, Paren(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Given(Formula conclusion, params Formula[] premises)
    {
        for (var index = premises.Length - 1; index >= 0; --index)
            conclusion = new Formula.Logic(Paren(premises[index]), FormulaLogicOperator.Implies, conclusion);
        return conclusion;
    }

    private static Formula Member(Formula value, Formula space) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, space);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Not(Formula value) => new Formula.Not(Paren(value));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Multiply(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pair(Formula a, Formula b) => Paren(Seq(a, Comma, Sp, b));
    private static Formula Component(Formula word, string component, Formula site) =>
        Apply(Seq(word, Dot, F.Id(component)), site);
    private static Formula Site(Formula index, Formula word) => Call("site", index, word);
    private static Formula Radical(Formula space) => Call("radical", space);
    private static Formula Orthogonal(Formula length, Formula space) =>
        Call("orthogonal", Call("spForm", length), space);
    private static Formula Intersection(Formula a, Formula b) => Call("inf", a, b);
    private static Formula Complement(Formula sites) => new Formula.Power(sites, F.Id("c"));
    private static Formula Zeros(Formula word) => Call("zeroCount", word);
    private static Formula Card(Formula sites) => Call("card", sites);
    private static Formula Support(Formula space) => Call("support", space);
    private static Formula Kernel(Formula space, Formula sites) => Call("siteKernel", space, sites);
    private static Formula Count(Formula space, Formula sites) => Call("kernelCount", space, sites);
    private static Formula Dim(Formula space) => Call("finrank", Field, space);
    private static Formula RestrictedRank(Formula space, Formula sites) =>
        Dim(Call("range", Call("domRestrict", Call("restrictSites", sites), space)));
    private static Formula Nonradical(Formula space, Formula conclusion) =>
        Given(conclusion, Member(V, space), Not(Member(V, Radical(space))));
    private static Formula WeightBound() =>
        All(V, Words(N), Nonradical(U, Le(Sub(N, D(3)), Sub(N, Zeros(V)))));
    private static Formula Filter(Formula variable, Formula predicate) =>
        Call("filter", Universe, Seq(variable, Sp, Mapsto, Sp, Paren(predicate)));
    private static Formula OccupiedSite() =>
        ExistsIn(V, Words(N), And(Member(V, W),
            new Formula.Relation(Site(SiteIndex, V), FormulaRelationOperator.NotEqual, D(0))));
    private static Formula OverSpaceAndSites(Formula body) =>
        AtLength(N, All(W, Spaces(N), All(I, SiteSets(N), body)));
    private static Formula CodeOfDimensions(Formula body, params Formula[] extra) =>
        AtLength(N, All(U, Spaces(N), Given(body, [
            Call("ZeroBound", U), Equal(Dim(U), D(8)), Equal(Dim(Radical(U)), D(4)), .. extra
        ])));

    private static Formula Attainment()
    {
        var attainingWord = ExistsIn(V, Words(N), And(Member(V, U),
            And(Not(Member(V, Radical(U))), Equal(Sub(N, Zeros(V)), Sub(N, D(3))))));
        var properties = And(Equal(Dim(U), D(8)),
            And(Equal(Dim(Radical(U)), D(4)), And(WeightBound(), attainingWord)));
        return Logic(Named("Attainment"), FormulaLogicOperator.Iff,
            ExistsIn(N, Nat, And(Le(D(6), N), ExistsIn(U, Spaces(N), properties))));
    }

    private static Formula KernelInequality()
    {
        var size = Card(I);
        var original = Count(U, I);
        var coefficient = Multiply(D(4), Paren(Sub(D(3), size)));
        var summand = Count(Radical(U), Call("insert", AddedSite, I));
        var sum = Seq(new Formula.Subscript(Sum, Member(AddedSite, Complement(I))), Sp, summand);
        var left = Add(Multiply(Paren(Sub(N, size)), original), Multiply(coefficient, Count(Radical(U), I)));
        var right = Add(Multiply(coefficient, original), Multiply(D(4), Paren(sum)));
        return AtLength(N, All(U, Spaces(N), Given(All(I, SiteSets(N), Le(left, right)), Call("ZeroBound", U))));
    }

    private static Formula PairBound(Formula length, Formula conclusion, params Formula[] extra) =>
        All(U, Spaces(length), Given(
            All(I, SiteSets(length), Given(conclusion, Equal(Card(I), D(2)))),
            [Call("ZeroBound", U), Equal(Dim(U), D(8)), .. extra]));

    private static Formula Mask()
    {
        var member = Member(SiteIndex, I);
        var maskedSite = Site(SiteIndex, Apply(Call("mask", I), V));
        var body = And(Given(Equal(maskedSite, Site(SiteIndex, V)), member),
            Given(Equal(maskedSite, D(0)), Not(member)));
        return AtLength(N, All(I, SiteSets(N), All(V, Words(N), All(SiteIndex, Sites(N), body))));
    }

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Entry(name, title, formula, DescribeRole.Definition, prose);

    private static DocumentBlock Theorem(string name, string title, Formula formula, string prose) =>
        Entry(name, title, formula, DescribeRole.Theorem, prose);

    private static DocumentBlock Entry(string name, string title, Formula formula, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Module + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
