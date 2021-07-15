#include "kernel/abstract.h"
#include "kernel/hott/hott.h"
#include "kernel/type_checker.h"
#include "kernel/environment.h"
#include "kernel/abstract_type_context.h"
#include "kernel/kernel_exception.h"
#include <vector>

namespace lean {

static name * g_hott_extension = nullptr;
static name * g_fibrant        = nullptr;
static name * g_Id             = nullptr;
static name * g_Id_refl        = nullptr;

struct hott_env_ext : public environment_extension {
    bool m_initialized;
    hott_env_ext():m_initialized(false){}
};

struct hott_env_ext_reg {
    unsigned m_ext_id;
    hott_env_ext_reg() { m_ext_id = environment::register_extension(std::make_shared<hott_env_ext>()); }
};

static hott_env_ext_reg * g_ext = nullptr;

static hott_env_ext const & get_extension(environment const & env) {
    return static_cast<hott_env_ext const &>(env.get_extension(g_ext->m_ext_id));
}

static environment update(environment const & env, hott_env_ext const & ext) {
    return env.update(g_ext->m_ext_id, std::make_shared<hott_env_ext>(ext));
}

static environment add_constant(environment const & env, name const & n, std::initializer_list<name> lvls, expr const & type) {
    auto cd = check(env, mk_constant_assumption(n, level_param_names(lvls), type));
    return env.add(cd);
}

environment declare_hott(environment const & env) {
    environment new_env = env;

    name u_name("u");
    level u = mk_param_univ(u_name);
    expr Sort_u = mk_sort(u);
    expr Type_u = mk_sort(mk_succ(u));
    expr Prop   = mk_Prop();

    expr alpha = mk_local("α", "α", Sort_u, mk_implicit_binder_info());
    expr a     = mk_local("a", alpha);

    /* constant {u} fibrant : Type u → Prop */
    new_env = add_constant(new_env, *g_fibrant, {u_name}, mk_arrow(Type_u, Prop));

    /* constant {u} Id {α : Sort u} : α → α → Sort u */
    new_env = add_constant(new_env, *g_Id, {u_name}, Pi(alpha, mk_arrow(alpha, mk_arrow(alpha, Sort_u))));

    /* constant {u} Id.refl {α : Sort u} (a : α) : Id a a */
    new_env = add_constant(
        new_env, *g_Id_refl, {u_name},
        Pi(alpha, Pi(a, mk_app(mk_constant(*g_Id, {u}), alpha, a, a)))
    );

    hott_env_ext ext = get_extension(env);
    if (ext.m_initialized)
        throw exception("failed to initialize HoTT module, already initialized");
    ext.m_initialized = true;
    return update(new_env, ext);
}

optional<expr> hott_normalizer_extension::operator()(expr const & e, abstract_type_context & ctx) const {
    return none_expr();
}

optional<expr> hott_normalizer_extension::is_stuck(expr const & e, abstract_type_context & ctx) const {
    return none_expr();
}

bool hott_normalizer_extension::supports(name const & feature) const {
    return feature == *g_hott_extension;
}

bool hott_normalizer_extension::is_recursor(environment const &, name const & n) const {
    return false;
}

bool hott_normalizer_extension::is_builtin(environment const & env, name const & n) const {
    if (!get_extension(env).m_initialized) return false;
    return n == *g_fibrant || n == *g_Id || n == *g_Id_refl;
}

void initialize_hott_module() {
    g_hott_extension = new name("hott_extension");
    g_fibrant        = new name{"fibrant"};
    g_Id             = new name{"Id"};
    g_Id_refl        = new name{"Id", "refl"};
    g_ext            = new hott_env_ext_reg();
}

void finalize_hott_module() {
    delete g_ext;
    delete g_hott_extension;

    delete g_Id_refl;
    delete g_Id;
    delete g_fibrant;
}

}