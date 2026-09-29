using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class SurjectiveColumnSharpWidthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One surjective column gives the optimal coefficient-one width bound and the sharp uniform real exponent.",
        H("A Surjective Column and Sharp Response Width"),
        Blocks(
            Paragraph(Text(
                "Let r and h be natural numbers with r>=1 and 0<=h<=r. For each 1<=i<=r, "
                + "let t_i be a Boolean coordinate and d_i a coordinate in an arbitrary finite "
                + "nonempty set D_i. There are two further coordinates a in A and b in B. "
                + "All 2r+2 coordinates are distinct, and inputs range over their full independent "
                + "product. The symbol mathbb B denotes the Boolean set; "
                + "the unadorned B denotes the alphabet of b. The task is "
                + "F(t,a,b,d)=G(t,psi(a,b)), so the d_i do not affect its value.")),
            Paragraph(Text(
                "Let I be the full set of labels and Omega_Q the product of the alphabets "
                + "at labels in Q. For a set P of coordinate labels, a prefix assignment x "
                + "in Omega_P fixes precisely P. "
                + "Its response R_P(x) is the function y |-> F(x joined with y), where y ranges "
                + "over the full product of the complementary labelled coordinates. Every prefix "
                + "at this cut has exactly this same suffix domain. Two prefixes are equivalent "
                + "exactly when these functions agree on every suffix. The capacity kappa_P(F) "
                + "is the number of distinct response functions, rather than the number of output values.")),
            Paragraph(Math(ResponseDefinitions())),
            Paragraph(Text(
                "Positions are numbered from zero. The order pi is "
                + "(t_1,...,t_h,a,t_(h+1),...,t_r,b,d_1,...,d_r), and rho is "
                + "(a,b,t_1,d_1,...,t_r,d_r). Thus pos_pi(a)=h, pos_pi(b)=r+1, "
                + "pos_pi(t_i)=i-1 for i<=h and i otherwise, and pos_pi(d_i)=r+1+i. "
                + "Also pos_rho(a)=0, pos_rho(b)=1, pos_rho(t_i)=2i, "
                + "and pos_rho(d_i)=2i+1. For either order eta, P_eta(k) contains the labels "
                + "whose positions are less than k. Width takes the maximum over every "
                + "k=0,...,2r+2, including the empty prefix and the final output layer.")),
            Paragraph(Text(
                "Write F_0 for the class of finite sets and F_+ for the finite nonempty sets. "
                + "The notation D in F_+^r means that each of the r alphabets D_i is finite "
                + "and nonempty. A map psi:A times B -> Z is written in curried form. "
                + "The condition psi(A,b_0)=Z refers to one fixed b_0 in B; it makes Z the "
                + "effective image and imposes no condition on any row or on the other columns. "
                + "All maps G are total. Write F_o(t,a,b,d)=o for a constant task.")),
            Paragraph(Text(
                "For every natural m>=2, put C_m=(Z/mZ)^(mathbb B^r), take A=B=Z=C_m, "
                + "and let psi(a,b)=a+b pointwise. Define the Boolean task "
                + "F_m(t,a,b,d) to be true exactly when (a+b)(t)=0. Both addition slices "
                + "are surjective. The alphabets D_i remain the same arbitrary fixed sets. "
                + "Write kappa_eta(m,k) for the actual response capacity of F_m at P_eta(k), "
                + "and W_m(eta) for its width. For 0<=k<=2r+2, the functions p and q "
                + "below give every raw layer.")),
            Paragraph(Math(LayerCounts())),
            Describe.Lean(
                DescribeId.Create("surjective-column-sharp-width"),
                DeclarationHandle.Create("D5/S3/Observer/Separation/SurjectiveColumnSharpWidth.result"),
                H("Coefficient one, all layer counts, and optimal uniform exponent"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the upper bound, let K_j be the capacity in pi after a and "
                        + "the first j selectors have been read, for h<=j<=r, and let W=W_F(pi). "
                        + "Each K_j is at most W. After a alone in rho, a response is determined "
                        + "by its restrictions at the 2^h assignments of the early selectors. "
                        + "Every restriction is an actual response at the K_h cut. This gives "
                        + "at most K_h^(2^h) possibilities.")),
                    Paragraph(Text(
                        "Choose a section sigma:Z->A of the surjective column, so "
                        + "psi(sigma(z),b_0)=z. After a,b and j<=h selectors in rho, "
                        + "the residual function is determined by its common-domain restrictions "
                        + "indexed by assignments of the early selectors. Each restriction is "
                        + "obtained from a K_h response by setting b=b_0. Hence the capacity "
                        + "is at most K_h^(2^h), without requiring arbitrary tuples of "
                        + "restrictions to be realizable. For j>h, each residual is instead "
                        + "the restriction at b_0 of a K_j response, giving capacity at most "
                        + "K_j. Reading an irrelevant d_i preserves the capacity: the common "
                        + "suffix projection is surjective and every shorter prefix lifts. "
                        + "The initial capacity is one and the final capacity is the image size. "
                        + "Since W>=1, every layer is bounded by W^(2^h).")),
                    Paragraph(Text(
                        "In the addition family, after j selectors and a, the response is "
                        + "specified by the selector prefix and its 2^(r-j) relevant entries "
                        + "of a. Different entry vectors are separated by a common suffix "
                        + "with b(t)=-a(t) at a differing entry. Different selector prefixes "
                        + "access different b entries, allowing one zero test to be true "
                        + "and the other false. The resulting count is exactly "
                        + "2^j m^(2^(r-j)). Before a, the same separation gives 2^j responses. "
                        + "After a,b in rho, every Boolean truth table occurs: independently "
                        + "choose each sum entry to be zero or one. After j selectors, all "
                        + "truth tables on the remaining r-j selectors still occur, giving "
                        + "2^(2^(r-j)). This also accounts for all intervening irrelevant layers.")),
                    Paragraph(Text(
                        "The counts 2^j m^(2^(r-j)) decrease as j increases from h to r, "
                        + "because m>=2. The two maxima are therefore exactly the displayed "
                        + "widths. For a smaller real exponent alpha, the ratio "
                        + "W_m(rho)/W_m(pi)^alpha equals "
                        + "2^(-h alpha) m^(2^r-alpha 2^(r-h)). Its exponent of m is positive "
                        + "precisely when alpha<2^h; increasing m defeats every fixed C>0. "
                        + "The cases h=0, h=r, r=1 and m=2 are included. Finally, a constant "
                        + "task has one response at every cut, so both widths are one and "
                        + "any uniform coefficient at exponent 2^h must be at least one."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Pow(Formula value, Formula exponent) => Seq(value, Caret, Grp(exponent));
    private static Formula Sub(Formula value, Formula index) => Seq(value, Underscore, Grp(index));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula App(Formula name, params Formula[] args) =>
        Seq(name, Open, Seq(args.SelectMany((arg, i) => i == 0
            ? new[] { arg } : new[] { Comma, Sp, arg }).ToArray()), Close);
    private static Formula All(Formula variables, Formula domain, Formula body) =>
        Seq(Forall, Sp, variables, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula Two(Formula exponent) => Pow(D(2), exponent);
    private static Formula Natural => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula FiniteSets => Sub(Seq(Mathcal, Grp(V("F"))), D(0));
    private static Formula NonemptySets => Sub(Seq(Mathcal, Grp(V("F"))), Plus);
    private static Formula Width(Formula task, Formula order) => App(Sub(V("W"), task), order);
    private static Formula Sharp(Formula order) => Width(V("m"), order);
    private static Formula Capacity(Formula order) => App(Sub(Kappa, order), V("m"), V("k"));
    private static Formula Gather(params Formula[] rows) => Seq(Begin, Grp(V("gathered")),
        Seq(rows.SelectMany((row, i) => i == 0 ? new[] { row }
            : new[] { RowBreak, row }).ToArray()), End, Grp(V("gathered")));

    private static Formula ResponseDefinitions()
    {
        Formula p = V("P"), x = V("x"), y = V("y"), k = V("k"), eta = V("e");
        return Disp(Gather(
            Seq(App(Sub(V("R"), p), x), Colon, Sp, Sub(Omega, Seq(V("I"), Setminus, Sp, p)),
                To, Sp, V("O"), Comma, Sp, y, Mapsto, Sp, App(V("F"), App(V("join"), x, y))),
            Seq(App(Sub(Kappa, p), V("F")), Eq, Lvert, OpenBrace,
                App(Sub(V("R"), p), x), Mid, Sp, x, InMacro, Sub(Omega, p), CloseBrace, Rvert),
            Seq(Width(V("F"), eta), Eq, Sub(Max, Seq(D(0), Leq, Sp, k, Leq,
                D(2), V("r"), Plus, D(2))), App(Sub(Kappa, App(Sub(V("P"), eta), k)), V("F")))));
    }

    private static Formula LayerCounts()
    {
        Formula r = V("r"), h = V("h"), m = V("m"), k = V("k");
        Formula before = Seq(Two(k), Amp, k, Leq, Sp, h);
        Formula middle = Seq(Two(Seq(k, Minus, D(1))), Pow(m, Two(Seq(r, Minus, Par(Seq(k, Minus, D(1)))))),
            Amp, h, Lt, k, Leq, Sp, r, Plus, D(1));
        Formula after = Seq(D(2), Amp, r, Plus, D(1), Lt, k);
        Formula normalized = Seq(Two(Two(Seq(r, Minus, Lfloor,
            Frac, Grp(Seq(k, Minus, D(1))), Grp(D(2)), Rfloor))), Amp, D(2), Leq, Sp, k);
        return Disp(Gather(
            Seq(Call("p", r, h, m, k), Eq, Begin, Grp(V("cases")),
                before, RowBreak, middle, RowBreak, after, End, Grp(V("cases"))),
            Seq(Call("q", r, m, k), Eq, Begin, Grp(V("cases")),
                D(1), Amp, k, Eq, D(0), RowBreak,
                Pow(m, Two(r)), Amp, k, Eq, D(1), RowBreak,
                normalized, End, Grp(V("cases")))));
    }

    private static Formula Statement()
    {
        Formula r = V("r"), h = V("h"), m = V("m"), k = V("k"), c = V("C");
        Formula a = V("A"), b = V("B"), z = V("Z"), o = V("O"), g = V("G");
        Formula bzero = Sub(V("b"), D(0));
        Formula selectors = Pow(Seq(Mathbb, Grp(V("B"))), r);
        Formula psiType = Seq(a, To, Sp, b, To, Sp, z);
        Formula prefix = All(Seq(r, Comma, h), Natural, Seq(D(1), Leq, Sp, r, Land, Sp, h, Leq, Sp, r,
            Implies, Forall, Sp, V("D"), InMacro, Pow(NonemptySets, r), Comma));
        Formula upper = All(Seq(a, Comma, b, Comma, o), NonemptySets,
            All(z, FiniteSets, All(Psi, psiType,
            All(g, Seq(selectors, To, Sp, z, To, Sp, o), All(bzero, b, Seq(
                App(Psi, a, bzero), Eq, z, Implies, Sp,
                Width(V("F"), Rho), Leq, Sp, Pow(Width(V("F"), Pi), Two(h))))))));
        Formula allLayers = All(k, Natural, Seq(k, Leq, D(2), r, Plus, D(2), Implies,
            Par(Seq(Capacity(Pi), Eq, Call("p", r, h, m, k), Land,
                Capacity(Rho), Eq, Call("q", r, m, k)))));
        Formula exact = All(m, Natural, Seq(D(2), Leq, Sp, m, Implies, Par(Seq(
            Par(allLayers), Land, Sp,
            Sharp(Pi), Eq, Two(h), Pow(m, Two(Seq(r, Minus, h))), Land, Sp,
            Sharp(Rho), Eq, Pow(m, Two(r))))));
        Formula sharp = All(Seq(Alpha, Comma, c), Real, Seq(Alpha, Lt, Two(h), Land,
            D(0), Lt, c, Implies, Exists, Sp, m, InMacro, Natural, Comma,
            D(2), Leq, Sp, m, Land, Sp, c, Pow(Sharp(Pi), Alpha), Lt, Sharp(Rho)));
        Formula constantTask = Sub(V("F"), V("o"));
        Formula constants = All(Seq(a, Comma, b), NonemptySets,
            All(Seq(z, Comma, o), FiniteSets, All(Psi, psiType, All(V("o"), o, Par(Seq(
                Width(constantTask, Pi), Eq, D(1), Land, Sp, Width(constantTask, Rho), Eq, D(1), Land,
                All(c, Real, Seq(Width(constantTask, Rho), Leq, Sp,
                    c, Pow(Width(constantTask, Pi), Two(h)), Implies, D(1), Leq, Sp, c))))))));
        return Disp(Gather(prefix, Par(upper), Land, Par(exact), Land, Par(sharp), Land, Par(constants)));
    }
}
