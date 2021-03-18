/*
TODO:
1) scale parameters of Line
2) vector -> &vector
3) store g[i][j]='1' if line goes through points i, j
*/

#pragma GCC optimize("Ofast")

#include <iostream>
#include <stdlib.h>
#include <cmath>
#include <algorithm>
#include <vector>
#include <queue>
#include <deque>
#include <set>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <random>
#include <assert.h>
#include <memory.h>
#include <time.h>
#include <bitset>

#define ll long long
#define ld long double
#define fi first
#define se second
#define sz(a) (int)a.size()

using namespace std;

const ll inf = (ll)2 * 1e9;
const ld pi = atan2(0, -1);
const ld eps = 1e-6;

void solve(int move_id, int cnt_moves, int curr_poss_move);

struct Point
{
    ld x, y;

    Point() {}
    Point(ld x, ld y) : x(x), y(y) {}

    ld len() { return sqrt(x * x + y * y); }

    void print() { cout << "Point: " << x << " " << y << endl; }

};

bool operator == (Point &p1, Point &p2) { return (abs(p1.x - p2.x) <= eps && abs(p1.y - p2.y) <= eps); }

bool operator != (Point &p1, Point &p2) { return !(p1 == p2); }

Point operator + (Point &p1, Point &p2) { return Point(p1.x + p2.x, p1.y + p2.y); }

Point operator - (Point &p1, Point &p2) { return Point(p1.x - p2.x, p1.y - p2.y); }

ld operator * (Point p1, Point p2) { return p1.x * p2.x + p1.y * p2.y; }

ld operator % (Point p1, Point p2) { return p1.x * p2.y - p2.x * p1.y; }

ld dist(Point &p1, Point &p2) { return sqrt((p1.x - p2.x) * (p1.x - p2.x) + (p1.y - p2.y) * (p1.y - p2.y)); }

Point no_s(-inf, -inf);
Point no_t(inf, inf);

struct Line // only Line/Segment
{
    ld a, b, c;
    Point s, t;

    Line() {}
    Line(ld a, ld b, ld c) : a(a), b(b), c(c) { s = no_s; t = no_t; }
    Line(Point &p1, Point &p2)
    {
        a = p1.y - p2.y;
        b = -(p1.x - p2.x);
        c = p1 % p2;
        s = no_s;
        t = no_t;
    }

    ld val(Point &p) { return a * p.x + b * p.y + c; }

    bool contains(Point &p) // check if point on Line lies on Line/Segment
    {
        if (s == no_s && t == no_t)
            return true;
        else
            return (s - p) * (t - p) <= eps;
    }

    void print(string name) { cout << name << ": " << a << "x + " << b << "y + " << c << " = 0" << endl; }

};

bool operator == (Line &l1, Line &l2)
{
    return (abs(l1.a * l2.b - l2.a * l1.b) <= eps) &&
        (abs(l1.a * l2.c - l2.a * l1.c) <= eps) &&
        (abs(l1.b * l2.c - l2.b * l1.c) <= eps) &&
        (l1.s == l2.s) && (l1.t == l2.t);
}

bool operator != (Line &l1, Line &l2)
{
    return !(l1 == l2);
}

Line Perpendicular(Line &l, Point &p)
{
    return Line(-l.b, l.a, l.b * p.x - l.a * p.y);
}

Line PerpendicularBisector(Point &p1, Point &p2)
{
    Line l(p1, p2);
    Point mid((p1.x + p2.x) / 2, (p1.y + p2.y) / 2);
    return Perpendicular(l, mid);
}

Line AngleBisector(Point &p1, Point &p2, Point &p3)
{
    ld dist1 = dist(p1, p2), dist2 = dist(p2, p3);
    Point tmp(p1.x + (p3.x - p1.x) / (dist1 + dist2) * dist1, p1.y + (p3.y - p1.y) / (dist1 + dist2) * dist1);
    return Line(p2, tmp);
}

Line ParallelLine(Line &l, Point &p)
{
    return Line(l.a, l.b, -l.a * p.x - l.b * p.y);
}

struct Circle
{
    ld x, y, r;

    Circle() {}
    Circle(ld x, ld y, ld r) : x(x), y(y), r(r) {}
    Circle(Point &p, ld r) : x(p.x), y(p.y), r(r) {}
    Circle(Point &p, Point &p1) : x(p.x), y(p.y), r(dist(p, p1)) {}

    public: void print(string name) { cout << name << ": (x - " << x << ")^2 + (y - " << y << ")^2 = " << r * r << endl; }

};

bool operator == (Circle &c1, Circle &c2)
{
    return (abs(c1.x - c2.x) <= eps) && (abs(c1.y - c2.y) <= eps) && (abs(c1.r - c2.r) <= eps);
}

bool operator != (Circle &c1, Circle &c2)
{
    return !(c1 == c2);
}

// Пересечение двух прямых
vector<Point> LIL(Line &l1, Line &l2)
{
    if (l1 == l2)
        return {};
    vector<Point> ans, ans1;
    if (abs(l1.a * l2.b - l2.a * l1.b) > eps)
        ans1.push_back(Point(-(l1.c * l2.b - l2.c * l1.b) / (l1.a * l2.b - l2.a * l1.b), -(l1.a * l2.c - l2.a * l1.c) / (l1.a * l2.b - l2.a * l1.b)));
    for (auto i : ans1)
        if (l1.contains(i) && l2.contains(i))
            ans.push_back(i);
    return ans;
}

// Переечение прямой и окружности
vector<Point> LIC(Line &l, Circle &c)
{
    vector<Point> ans, ans1;
    ld dx = c.x, dy = c.y;
    c.x -= dx; c.y -= dy; l.c += (l.a * dx + l.b * dy);
    ld x0 = -l.a * l.c / (l.a * l.a + l.b * l.b), y0 = -l.b * l.c / (l.a * l.a + l.b * l.b);
    if (l.c * l.c - c.r * c.r * (l.a * l.a + l.b * l.b) > eps)
    {
        c.x += dx; c.y += dy; l.c -= (l.a * dx + l.b * dy);
        return {};
    }
    else if (abs(l.c * l.c - c.r * c.r * (l.a * l.a + l.b * l.b)) <= eps)
    {
        x0 += dx; y0 += dy;
        ans1.push_back(Point(x0, y0));
        for (auto i : ans1)
            if (l.contains(i))
                ans.push_back(i);
        c.x += dx; c.y += dy; l.c -= (l.a * dx + l.b * dy);
        return ans;
    }
    else
    {
        ld d = c.r * c.r - l.c * l.c / (l.a * l.a + l.b * l.b);
        ld mult = sqrt(d / (l.a * l.a + l.b * l.b));
        ld ax, ay, bx, by;
        ax = x0 + l.b * mult;
        bx = x0 - l.b * mult;
        ay = y0 - l.a * mult;
        by = y0 + l.a * mult;
        ax += dx; ay += dy; bx += dx; by += dy;
        ans1.push_back(Point(ax, ay));
        ans1.push_back(Point(bx, by));
        for (auto i : ans1)
            if (l.contains(i))
                ans.push_back(i);
        c.x += dx; c.y += dy; l.c -= (l.a * dx + l.b * dy);
        return ans;
    }
}

// Пересечение двух окружностей
vector<Point> CIC(Circle &c1, Circle &c2)
{
    if (c1 == c2)
        return {};
    ld dx = c1.x, dy = c1.y;
    c1.x -= dx; c1.y -= dy; c2.x -= dx; c2.y -= dy;
    Line tmp(-2 * c2.x, -2 * c2.y, c2.x * c2.x + c2.y * c2.y + c1.r * c1.r - c2.r * c2.r);
    vector<Point> ans = LIC(tmp, c1);
    for (int i = 0; i < sz(ans); i++)
    {
        ans[i].x += dx;
        ans[i].y += dy;
    }
    c1.x += dx; c1.y += dy; c2.x += dx; c2.y += dy;
    return ans;
}

vector<Point> points;
vector<Line> lines;
vector<Circle> circles;

vector<Point> anspoints;
vector<Line> anslines;
vector<Circle> anscircles;
int ok_points, ok_lines, ok_circles;

vector<Line> poss_lines;
vector<Circle> poss_circles;
vector<pair<int, int> > poss_moves;

void init_ans()
{
    ok_points = (1 << (int)anspoints.size()) - 1;
    for (int i = 0; i < (int)anspoints.size(); i++)
        for (int j = 0; j < (int)points.size(); j++)
            if (anspoints[i] == points[j])
            {
                ok_points ^= (1 << i);
                break;
            }
    ok_lines = (1 << (int)anslines.size()) - 1;
    for (int i = 0; i < (int)anslines.size(); i++)
        for (int j = 0; j < (int)lines.size(); j++)
            if (anslines[i] == lines[j])
            {
                ok_lines ^= (1 << i);
                break;
            }
    ok_circles = (1 << (int)anscircles.size()) - 1;
    for (int i = 0; i < (int)anscircles.size(); i++)
        for (int j = 0; j < (int)circles.size(); j++)
            if (anscircles[i] == circles[j])
            {
                ok_circles ^= (1 << i);
                break;
            }
}

int get_ans_points(Point &p)
{
    int new_points = 0;
    for (int i = 0; i < (int)anspoints.size(); i++)
        if (((ok_points >> i) & 1) && (p == anspoints[i]))
            new_points |= (1 << i);
    return new_points;
}

int get_ans_lines(Line &l)
{
    int new_lines = 0;
    for (int i = 0; i < (int)anslines.size(); i++)
        if (((ok_lines >> i) & 1) && (l == anslines[i]))
            new_lines |= (1 << i);
    return new_lines;
}

int get_ans_circles(Circle &c)
{
    int new_circles = 0;
    for (int i = 0; i < (int)anscircles.size(); i++)
        if (((ok_circles >> i) & 1) && (c == anscircles[i]))
            new_circles |= (1 << i);
    return new_circles;
}

bool accept()
{
    return (ok_points | ok_lines | ok_circles) == 0;
}

vector<pair<string, int> > pos;
vector<vector<bool> > moves;
int ttt = 0;

bool used(Point &p)
{
    for (int i = 0; i < sz(points); i++)
        if (p == points[i])
            return true;
    return false;
}

bool used(Line &l)
{
    for (int i = 0; i < sz(lines); i++)
        if (l == lines[i])
            return true;
    return false;
}

bool used(Circle &c)
{
    for (int i = 0; i < sz(circles); i++)
        if (c == circles[i])
            return true;
    return false;
}

bool used_poss(Line &l)
{
    for (int i = 0; i < sz(poss_lines); i++)
        if (l == poss_lines[i])
            return true;
    return false;
}

bool used_poss(Circle &c)
{
    for (int i = 0; i < sz(poss_circles); i++)
        if (c == poss_circles[i])
            return true;
    return false;
}

void add_possible_moves(int &cnt_add_points, int &cnt_poss_moves)
{
    // add new possible lines
    for (int i = sz(points) - 1; i >= sz(points) - cnt_add_points; i--)
        for (int j = i - 1; j >= 0; j--)
        {
            assert(points[i] != points[j]);
            Line new_line(points[i], points[j]);
            if (!used(new_line) && !used_poss(new_line))
            {
                poss_moves.push_back({0, sz(poss_lines)});
                poss_lines.push_back(new_line);
                cnt_poss_moves++;
            }
        }
    // add new possible circles
    for (int i = sz(points) - 1; i >= sz(points) - cnt_add_points; i--)
        for (int j = i - 1; j >= 0; j--)
        {
            assert(points[i] != points[j]);
            Circle new_circle(points[i], points[j]);
            if (!used(new_circle) && !used_poss(new_circle))
            {
                poss_moves.push_back({1, sz(poss_circles)});
                poss_circles.push_back(new_circle);
                cnt_poss_moves++;
            }
            new_circle = Circle(points[j], points[i]);
            if (!used(new_circle) && !used_poss(new_circle))
            {
                poss_moves.push_back({1, sz(poss_circles)});
                poss_circles.push_back(new_circle);
                cnt_poss_moves++;
            }
        }
}

void addLine(Line &l, int &cnt_add_points, int &cnt_poss_moves, int &new_lines, int &new_points)
{
    lines.push_back(l);
    cnt_add_points = 0; cnt_poss_moves = 0; new_lines = 0; new_points = 0;
    new_lines = get_ans_lines(l);
    for (Line &line : lines)
    {
        vector<Point> curr = LIL(l, line);
        for (Point &p : curr)
            if (!used(p))
            {
                points.push_back(p);
                new_points |= get_ans_points(p);
                cnt_add_points++;
            }
    }
    for (Circle &circle : circles)
    {
        vector<Point> curr = LIC(l, circle);
        for (Point &p : curr)
            if (!used(p))
            {
                points.push_back(p);
                new_points |= get_ans_points(p);
                cnt_add_points++;
            }
    }
    add_possible_moves(cnt_add_points, cnt_poss_moves);
}

void addCircle(Circle &c, int &cnt_add_points, int &cnt_poss_moves, int &new_circles, int &new_points)
{
    circles.push_back(c);
    cnt_add_points = 0; cnt_poss_moves = 0; new_circles = 0; new_points = 0;
    new_circles = get_ans_circles(c);
    for (Line &line : lines)
    {
        vector<Point> curr = LIC(line, c);
        for (Point &p : curr)
            if (!used(p))
            {
                points.push_back(p);
                new_points |= get_ans_points(p);
                cnt_add_points++;
            }
    }
    for (Circle &circle : circles)
    {
        vector<Point> curr = CIC(c, circle);
        for (Point &p : curr)
            if (!used(p))
            {
                points.push_back(p);
                new_points |= get_ans_points(p);
                cnt_add_points++;
            }
    }
    add_possible_moves(cnt_add_points, cnt_poss_moves);
}

void print_solution()
{
    cout << sz(pos) << endl;
    for (int i = 0; i < sz(pos); i++)
    {
        cout << i + 1 << " : ";
        if (pos[i].first == "Circle" || pos[i].first == "Compass")
            circles[pos[i].second].print(pos[i].first);
        else
            lines[pos[i].second].print(pos[i].first);
    }
    cout << endl << endl;
}

void solve(int move_id, int cnt_moves, int curr_poss_move)
{
    ttt++;
    if (move_id == cnt_moves)
    {
        if (accept())
            print_solution();
        return;
    }
    if (accept())
    {
        print_solution();
        return;
    }
    if (curr_poss_move >= sz(poss_moves))
        return;
    if (curr_poss_move + 1 < sz(poss_moves))
        solve(move_id, cnt_moves, curr_poss_move + 1);
    if (poss_moves[curr_poss_move].fi == 0)
    {
        // Line
        int cnt_add_points, cnt_poss_moves, new_lines, new_points;
        pos.push_back({"Line", sz(lines)});
        addLine(poss_lines[poss_moves[curr_poss_move].se], cnt_add_points, cnt_poss_moves, new_lines, new_points);
        ok_lines ^= new_lines;
        ok_points ^= new_points;
        solve(move_id + 1, cnt_moves, curr_poss_move + 1);
        pos.pop_back();
        lines.pop_back();
        for (int k = 0; k < cnt_add_points; k++)
            points.pop_back();
        for (int k = 0; k < cnt_poss_moves; k++)
        {
            if (poss_moves.back().fi == 0)
                poss_lines.pop_back();
            else
                poss_circles.pop_back();
            poss_moves.pop_back();
        }
        ok_lines ^= new_lines;
        ok_points ^= new_points;
    }
    else
    {
        //Circle
        int cnt_add_points, cnt_poss_moves, new_circles, new_points;
        pos.push_back({"Circle", sz(circles)});
        addCircle(poss_circles[poss_moves[curr_poss_move].se], cnt_add_points, cnt_poss_moves, new_circles, new_points);
        ok_circles ^= new_circles;
        ok_points ^= new_points;
        solve(move_id + 1, cnt_moves, curr_poss_move + 1);
        pos.pop_back();
        circles.pop_back();
        for (int k = 0; k < cnt_add_points; k++)
            points.pop_back();
        for (int k = 0; k < cnt_poss_moves; k++)
        {
            if (poss_moves.back().fi == 0)
                poss_lines.pop_back();
            else
                poss_circles.pop_back();
            poss_moves.pop_back();
        }
        ok_circles ^= new_circles;
        ok_points ^= new_points;
    }
}

int main()
{
    //freopen("a.in", "r", stdin);
    //freopen("a.out", "w", stdout);
    //ios_base::sync_with_stdio(0);
    //cin.tie(0);
    setlocale(LC_CTYPE, "rus");
    cout.precision(20);
    cout << fixed;
    cout << "Введите входные данные\n";
    cout << "Чтобы закончить ввод данных введите end\n";
    while (true)
    {
        string s;
        cin >> s;
        if (s == "end")
            break;
        if (s == "point")
        {
            cout << "Введите координаты точки через пробел\n";
            ld x, y;
            cin >> x >> y;
            points.push_back(Point(x, y));
        }
        else if (s == "line")
        {
            while (true)
            {
                cout << "Выберите 2 точки, через которые должна проходить прямая, и введите их номера через пробел\n";
                cout << "А также выведите 0, если хотите добавить прямую, и 1, если отрезок\n";
                for (int i = 0; i < sz(points); i++)
                    cout << i + 1 << "   " << points[i].x << " " << points[i].y << endl;
                int n1, n2, n3;
                cin >> n1 >> n2 >> n3;
                n1--; n2--;
                if (n1 == n2)
                    cout << "Выберите разные точки\n";
                else if (n1 >= sz(points) || n2 >= sz(points) || n1 < 0 || n2 < 0 || (n3 != 0 && n3 != 1))
                    cout << "Введите номер существующей точки\n";
                else
                {
                    Line currline = Line(points[n1], points[n2]);
                    if (n3 == 1)
                    {
                        currline.s = points[n1];
                        currline.t = points[n2];
                    }
                    int tmp;
                    addLine(currline, tmp, tmp, tmp, tmp);
                    currline.print("Добавлена прямая");
                    break;
                }
            }
        }
        else if (s == "circle")
        {
            while (true)
            {
                cout << "Выберите 2 точки, центр и точка на окружности, и введите их номера через пробел\n";
                for (int i = 0; i < sz(points); i++)
                    cout << i + 1 << "   " << points[i].x << " " << points[i].y << endl;
                int n1, n2;
                cin >> n1 >> n2;
                n1--; n2--;
                if (n1 == n2)
                    cout << "Выберите разные точки\n";
                else if (n1 >= sz(points) || n2 >= sz(points) || n1 < 0 || n2 < 0)
                    cout << "Введите номер существующей точки\n";
                else
                {
                    Circle currcircle = Circle(points[n1].x, points[n1].y, dist(points[n1], points[n2]));
                    int tmp;
                    addCircle(currcircle, tmp, tmp, tmp, tmp);
                    currcircle.print("Добавлена окружность");
                    break;
                }
            }
        }
        else if (s == "delpoint")
        {
            cout << "Выберите точку, которую вы хотите удалить\n";
            for (int i = 0; i < sz(points); i++)
                cout << i + 1 << "   " << points[i].x << " " << points[i].y << endl;
            int n;
            cin >> n;
            n--;
            for (int i = n; i < sz(points); i++)
                points[i] = points[i + 1];
            points.pop_back();
        }
        else
        {
            cout << "Введите point или line или circle или delpoint или end\n";
        }
    }
    poss_moves.clear(); poss_lines.clear(); poss_circles.clear();
    int cnt_add_points = sz(points), cnt_poss_moves;
    add_possible_moves(cnt_add_points, cnt_poss_moves);

    cout << "Введите искомое построение\n"; //Should not contain lines and circles from input
    while (true)
    {
        string s;
        cin >> s;
        if (s == "end")
            break;
        if (s == "point")
        {
            cout << "Введите координаты точки через пробел\n";
            ld x, y;
            cin >> x >> y;
            anspoints.push_back(Point(x, y));
        }
        else if (s == "line")
        {
            cout << "Введите координаты двух точек через пробел\n";
            ld x1, y1, x2, y2;
            cin >> x1 >> y1 >> x2 >> y2;
            Point p1(x1, y1), p2(x2, y2);
            anslines.push_back(Line(p1, p2));
        }
        else if (s == "circle")
        {
            cout << "Введите координаты центра и точки на окружности\n";
            ld x1, y1, x2, y2;
            cin >> x1 >> y1 >> x2 >> y2;
            Point p1(x1, y1), p2(x2, y2);
            anscircles.push_back(Circle(x1, y1, dist(p1, p2)));
        }
        else
            cout << "Введите point или line или circle или end\n";
    }
    cout << "Введите количество ходов\n";
    int n;
    cin >> n;
    cout << "\n\n\n";
    clock_t time = clock();
    // freopen("euclidea.txt", "w", stdout);
    init_ans();
    solve(0, n, 0);
    cout << ttt << endl;
    cout << clock() - time << endl;
    return 0;
}
