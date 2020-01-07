// Tank2 ��Ϸ��������
// �������
// ���ߣ�289371298 upgraded from zhouhy
// https://www.botzone.org.cn/games/Tank2

#include <stack>
#include <set>
#include <string>
#include <iostream>
#include <ctime>
#include <cstring>
#include <queue>
#include<math.h>
#ifdef _BOTZONE_ONLINE
#include "jsoncpp/json.h"
#else
#include "jsoncpp\json.h"
#endif

using std::string;
using std::cin;
using std::cout;
using std::endl;
using std::flush;
using std::getline;
using std::queue;
namespace TankGame
{
	using std::stack;
	using std::set;
	using std::istream;

#ifdef _MSC_VER
#pragma region ���������˵��
#endif

	enum GameResult
	{
		NotFinished = -2,
		Draw = -1,
		Blue = 0,
		Red = 1
	};

	enum FieldItem
	{
		None = 0,
		Brick = 1,
		Steel = 2,
		Base = 4,
		Blue0 = 8,
		Blue1 = 16,
		Red0 = 32,
		Red1 = 64,
		Water = 128
	};

	template<typename T> inline T operator~ (T a) { return (T)~(int)a; }
	template<typename T> inline T operator| (T a, T b) { return (T)((int)a | (int)b); }
	template<typename T> inline T operator& (T a, T b) { return (T)((int)a & (int)b); }
	template<typename T> inline T operator^ (T a, T b) { return (T)((int)a ^ (int)b); }
	template<typename T> inline T& operator|= (T& a, T b) { return (T&)((int&)a |= (int)b); }
	template<typename T> inline T& operator&= (T& a, T b) { return (T&)((int&)a &= (int)b); }
	template<typename T> inline T& operator^= (T& a, T b) { return (T&)((int&)a ^= (int)b); }

	enum Action
	{
		Invalid = -2,
		Stay = -1,
		Up, Right, Down, Left,
		UpShoot, RightShoot, DownShoot, LeftShoot
	};

	// �������Ͻ�Ϊԭ�㣨0, 0����x ���������죬y ����������
	// Side����ս˫���� - 0 Ϊ����1 Ϊ��
	// Tank��ÿ����̹�ˣ� - 0 Ϊ 0 ��̹�ˣ�1 Ϊ 1 ��̹��
	// Turn���غϱ�ţ� - �� 1 ��ʼ

	const int fieldHeight = 9, fieldWidth = 9, sideCount = 2, tankPerSide = 2;

	// ���صĺ�����
	const int baseX[sideCount] = { fieldWidth / 2, fieldWidth / 2 };

	// ���ص�������
	const int baseY[sideCount] = { 0, fieldHeight - 1 };

	const int dx[4] = { 0, 1, 0, -1 }, dy[4] = { -1, 0, 1, 0 };
	const FieldItem tankItemTypes[sideCount][tankPerSide] = {
		{ Blue0, Blue1 },{ Red0, Red1 }
	};

	int maxTurn = 100;

#ifdef _MSC_VER
#pragma endregion

#pragma region ���ߺ�������
#endif

	inline bool ActionIsMove(Action x)
	{
		return x >= Up && x <= Left;
	}

	inline bool ActionIsShoot(Action x)
	{
		return x >= UpShoot && x <= LeftShoot;
	}

	inline bool ActionDirectionIsOpposite(Action a, Action b)
	{
		return a >= Up && b >= Up && (a + 2) % 4 == b % 4;
	}

	inline bool CoordValid(int x, int y)
	{
		return x >= 0 && x < fieldWidth && y >= 0 && y < fieldHeight;
	}

	// �ж� item �ǲ��ǵ���һ��Ķ��̹��
	inline bool HasMultipleTank(FieldItem item)
	{
		// ���������ֻ��һ���������ô item ��ֵ�� 2 ���ݻ� 0
		// �������� x��x & (x - 1) == 0 ���ҽ��� x �� 2 ���ݻ� 0
		return !!(item & (item - 1));
	}

	inline int GetTankSide(FieldItem item)
	{
		return item == Blue0 || item == Blue1 ? Blue : Red;
	}

	inline int GetTankID(FieldItem item)
	{
		return item == Blue0 || item == Red0 ? 0 : 1;
	}

	// ��ö����ķ���
	inline int ExtractDirectionFromAction(Action x)
	{
		if (x >= Up)
			return x % 4;
		return -1;
	}

	// �����ʧ�ļ�¼�����ڻ���
	struct DisappearLog
	{
		FieldItem item;

		// ��������ʧ�Ļغϵı��
		int turn;

		int x, y;
		bool operator< (const DisappearLog& b) const
		{
			if (x == b.x)
			{
				if (y == b.y)
					return item < b.item;
				return y < b.y;
			}
			return x < b.x;
		}
	};

#ifdef _MSC_VER
#pragma endregion

#pragma region TankField ��Ҫ�߼���
#endif

	class TankField
	{
	public:
		//!//!//!// ���±������Ϊֻ�������Ƽ������޸� //!//!//!//

		// ��Ϸ�����ϵ������һ�������Ͽ����ж��̹�ˣ�
		FieldItem gameField[fieldHeight][fieldWidth] = {};

		// ̹���Ƿ���
		bool tankAlive[sideCount][tankPerSide] = { { true, true },{ true, true } };

		// �����Ƿ���
		bool baseAlive[sideCount] = { true, true };

		// ̹�˺����꣬-1��ʾ̹����ը
		int tankX[sideCount][tankPerSide] = {
			{ fieldWidth / 2 - 2, fieldWidth / 2 + 2 },{ fieldWidth / 2 + 2, fieldWidth / 2 - 2 }
		};

		// ̹�������꣬-1��ʾ̹����ը
		int tankY[sideCount][tankPerSide] = { { 0, 0 },{ fieldHeight - 1, fieldHeight - 1 } };

		// ��ǰ�غϱ��
		int currentTurn = 1;

		// ������һ��
		int mySide;

		// ���ڻ��˵�log
		stack<DisappearLog> logs;

		// ����������previousActions[x] ��ʾ�������ڵ� x �غϵĶ������� 0 �غϵĶ���û�����壩
		Action previousActions[101][sideCount][tankPerSide] = { { { Stay, Stay },{ Stay, Stay } } };

		//!//!//!// ���ϱ������Ϊֻ�������Ƽ������޸� //!//!//!//

		// ���غ�˫������ִ�еĶ�������Ҫ�ֶ�����
		Action nextAction[sideCount][tankPerSide] = { { Invalid, Invalid },{ Invalid, Invalid } };

		// �ж���Ϊ�Ƿ�Ϸ���������ƶ����ǿո��������Ƿ���
		// δ����̹���Ƿ���
		bool ActionIsValid(int side, int tank, Action act)
		{
			if (act == Invalid)
				return false;
			if (act > Left && previousActions[currentTurn - 1][side][tank] > Left) // �������غ����
				return false;
			if (act == Stay || act > Left)
				return true;
			int x = tankX[side][tank] + dx[act],
				y = tankY[side][tank] + dy[act];
			return CoordValid(x, y) && gameField[y][x] == None;// water cannot be stepped on
		}

		// �ж� nextAction �е�������Ϊ�Ƿ񶼺Ϸ�
		// ���Ե�δ����̹��
		bool ActionIsValid()
		{
			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
					if (tankAlive[side][tank] && !ActionIsValid(side, tank, nextAction[side][tank]))
						return false;
			return true;
		}

	private:
		void _destroyTank(int side, int tank)
		{
			tankAlive[side][tank] = false;
			tankX[side][tank] = tankY[side][tank] = -1;
		}

		void _revertTank(int side, int tank, DisappearLog& log)
		{
			int &currX = tankX[side][tank], &currY = tankY[side][tank];
			if (tankAlive[side][tank])
				gameField[currY][currX] &= ~tankItemTypes[side][tank];
			else
				tankAlive[side][tank] = true;
			currX = log.x;
			currY = log.y;
			gameField[currY][currX] |= tankItemTypes[side][tank];
		}
	public:

		// ִ�� nextAction ��ָ������Ϊ��������һ�غϣ�������Ϊ�Ƿ�Ϸ�
		bool DoAction()
		{
			if (!ActionIsValid())
				return false;

			// 1 �ƶ�
			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
				{
					Action act = nextAction[side][tank];

					// ���涯��
					previousActions[currentTurn][side][tank] = act;
					if (tankAlive[side][tank] && ActionIsMove(act))
					{
						int &x = tankX[side][tank], &y = tankY[side][tank];
						FieldItem &items = gameField[y][x];

						// ��¼ Log
						DisappearLog log;
						log.x = x;
						log.y = y;
						log.item = tankItemTypes[side][tank];
						log.turn = currentTurn;
						logs.push(log);

						// �������
						x += dx[act];
						y += dy[act];

						// ������ǣ�ע����ӿ����ж��̹�ˣ�
						gameField[y][x] |= log.item;
						items &= ~log.item;
					}
				}

			// 2 ����!
			set<DisappearLog> itemsToBeDestroyed;
			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
				{
					Action act = nextAction[side][tank];
					if (tankAlive[side][tank] && ActionIsShoot(act))
					{
						int dir = ExtractDirectionFromAction(act);
						int x = tankX[side][tank], y = tankY[side][tank];
						bool hasMultipleTankWithMe = HasMultipleTank(gameField[y][x]);
						while (true)
						{
							x += dx[dir];
							y += dy[dir];
							if (!CoordValid(x, y))
								break;
							FieldItem items = gameField[y][x];
							//tank will not be on water, and water will not be shot, so it can be handled as None
							if (items != None && items != Water)
							{
								// �����ж�
								if (items >= Blue0 &&
									!hasMultipleTankWithMe && !HasMultipleTank(items))
								{
									// �Լ�������䵽��Ŀ����Ӷ�ֻ��һ��̹��
									Action theirAction = nextAction[GetTankSide(items)][GetTankID(items)];
									if (ActionIsShoot(theirAction) &&
										ActionDirectionIsOpposite(act, theirAction))
									{
										// �����ҷ��ͶԷ�����������Ƿ���
										// ��ô�ͺ���������
										break;
									}
								}

								// �����Щ���Ҫ���ݻ��ˣ���ֹ�ظ��ݻ٣�
								for (int mask = 1; mask <= Red1; mask <<= 1)
									if (items & mask)
									{
										DisappearLog log;
										log.x = x;
										log.y = y;
										log.item = (FieldItem)mask;
										log.turn = currentTurn;
										itemsToBeDestroyed.insert(log);
									}
								break;
							}
						}
					}
				}

			for (auto& log : itemsToBeDestroyed)
			{
				switch (log.item)
				{
				case Base:
				{
					int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
					baseAlive[side] = false;
					break;
				}
				case Blue0:
					_destroyTank(Blue, 0);
					break;
				case Blue1:
					_destroyTank(Blue, 1);
					break;
				case Red0:
					_destroyTank(Red, 0);
					break;
				case Red1:
					_destroyTank(Red, 1);
					break;
				case Steel:
					continue;
				default:
					;
				}
				gameField[log.y][log.x] &= ~log.item;
				logs.push(log);
			}

			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
					nextAction[side][tank] = Invalid;

			currentTurn++;
			return true;
		}

		// �ص���һ�غ�
		bool Revert()
		{
			if (currentTurn == 1)
				return false;

			currentTurn--;
			while (!logs.empty())
			{
				DisappearLog& log = logs.top();
				if (log.turn == currentTurn)
				{
					logs.pop();
					switch (log.item)
					{
					case Base:
					{
						int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
						baseAlive[side] = true;
						gameField[log.y][log.x] = Base;
						break;
					}
					case Brick:
						gameField[log.y][log.x] = Brick;
						break;
					case Blue0:
						_revertTank(Blue, 0, log);
						break;
					case Blue1:
						_revertTank(Blue, 1, log);
						break;
					case Red0:
						_revertTank(Red, 0, log);
						break;
					case Red1:
						_revertTank(Red, 1, log);
						break;
					default:
						;
					}
				}
				else
					break;
			}
			return true;
		}

		// ��Ϸ�Ƿ������˭Ӯ�ˣ�
		GameResult GetGameResult()
		{
			bool fail[sideCount] = {};
			for (int side = 0; side < sideCount; side++)
				if ((!tankAlive[side][0] && !tankAlive[side][1]) || !baseAlive[side])
					fail[side] = true;
			if (fail[0] == fail[1])
				return fail[0] || currentTurn > maxTurn ? Draw : NotFinished;
			if (fail[Blue])
				return Red;
			return Blue;
		}

		/* ���� int ��ʾ���� 01 ����ÿ�� int �� 27 λ��ʾ 3 �У�
		   initialize gameField[][]
		   brick>water>steel
		*/
		TankField(int hasBrick[3], int hasWater[3], int hasSteel[3], int mySide) : mySide(mySide)
		{
			for (int i = 0; i < 3; i++)
			{
				int mask = 1;
				for (int y = i * 3; y < (i + 1) * 3; y++)
				{
					for (int x = 0; x < fieldWidth; x++)
					{
						if (hasBrick[i] & mask)
							gameField[y][x] = Brick;
						else if (hasWater[i] & mask)
							gameField[y][x] = Water;
						else if (hasSteel[i] & mask)
							gameField[y][x] = Steel;
						mask <<= 1;
					}
				}
			}
			for (int side = 0; side < sideCount; side++)
			{
				for (int tank = 0; tank < tankPerSide; tank++)
					gameField[tankY[side][tank]][tankX[side][tank]] = tankItemTypes[side][tank];
				gameField[baseY[side]][baseX[side]] = Base;
			}
		}
		// ��ӡ����
		void DebugPrint()
		{
#ifndef _BOTZONE_ONLINE
			const string side2String[] = { "��", "��" };
			const string boolean2String[] = { "��ը", "���" };
			const char* boldHR = "==============================";
			const char* slimHR = "------------------------------";
			cout << boldHR << endl
				<< "ͼ����" << endl
				<< ". - ��\t# - ש\t% - ��\t* - ����\t@ - ���̹��" << endl
				<< "b - ��0\tB - ��1\tr - ��0\tR - ��1\tW - ˮ" << endl //Tank2 feature
				<< slimHR << endl;
			for (int y = 0; y < fieldHeight; y++)
			{
				for (int x = 0; x < fieldWidth; x++)
				{
					switch (gameField[y][x])
					{
					case None:
						cout << '.';
						break;
					case Brick:
						cout << '#';
						break;
					case Steel:
						cout << '%';
						break;
					case Base:
						cout << '*';
						break;
					case Blue0:
						cout << 'b';
						break;
					case Blue1:
						cout << 'B';
						break;
					case Red0:
						cout << 'r';
						break;
					case Red1:
						cout << 'R';
						break;
					case Water:
						cout << 'W';
						break;
					default:
						cout << '@';
						break;
					}
				}
				cout << endl;
			}
			cout << slimHR << endl;
			for (int side = 0; side < sideCount; side++)
			{
				cout << side2String[side] << "������" << boolean2String[baseAlive[side]];
				for (int tank = 0; tank < tankPerSide; tank++)
					cout << ", ̹��" << tank << boolean2String[tankAlive[side][tank]];
				cout << endl;
			}
			cout << "��ǰ�غϣ�" << currentTurn << "��";
			GameResult result = GetGameResult();
			if (result == -2)
				cout << "��Ϸ��δ����" << endl;
			else if (result == -1)
				cout << "��Ϸƽ��" << endl;
			else
				cout << side2String[result] << "��ʤ��" << endl;
			cout << boldHR << endl;
#endif
		}

		bool operator!= (const TankField& b) const
		{

			for (int y = 0; y < fieldHeight; y++)
				for (int x = 0; x < fieldWidth; x++)
					if (gameField[y][x] != b.gameField[y][x])
						return true;

			for (int side = 0; side < sideCount; side++)
				for (int tank = 0; tank < tankPerSide; tank++)
				{
					if (tankX[side][tank] != b.tankX[side][tank])
						return true;
					if (tankY[side][tank] != b.tankY[side][tank])
						return true;
					if (tankAlive[side][tank] != b.tankAlive[side][tank])
						return true;
				}

			if (baseAlive[0] != b.baseAlive[0] ||
				baseAlive[1] != b.baseAlive[1])
				return true;

			if (currentTurn != b.currentTurn)
				return true;

			return false;
		}
	};

#ifdef _MSC_VER
#pragma endregion
#endif

	TankField *field;

#ifdef _MSC_VER
#pragma region ��ƽ̨��������
#endif

	// �ڲ�����
	namespace Internals
	{
		Json::Reader reader;
#ifdef _BOTZONE_ONLINE
		Json::FastWriter writer;
#else
		Json::StyledWriter writer;
#endif

		void _processRequestOrResponse(Json::Value& value, bool isOpponent)
		{
			if (value.isArray())
			{
				if (!isOpponent)
				{
					for (int tank = 0; tank < tankPerSide; tank++)
						field->nextAction[field->mySide][tank] = (Action)value[tank].asInt();
				}
				else
				{
					for (int tank = 0; tank < tankPerSide; tank++)
						field->nextAction[1 - field->mySide][tank] = (Action)value[tank].asInt();
					field->DoAction();
				}
			}
			else
			{
				// �ǵ�һ�غϣ������ڽ��ܳ���
				int hasBrick[3], hasWater[3], hasSteel[3];
				for (int i = 0; i < 3; i++) {//Tank2 feature(???????????????)
					hasWater[i] = value["waterfield"][i].asInt();
					hasBrick[i] = value["brickfield"][i].asInt();
					hasSteel[i] = value["steelfield"][i].asInt();
				}
				field = new TankField(hasBrick, hasWater, hasSteel, value["mySide"].asInt());
			}
		}

		// ��ʹ�� SubmitAndExit ���� SubmitAndDontExit
		void _submitAction(Action tank0, Action tank1, string debug = "", string data = "", string globaldata = "")
		{
			Json::Value output(Json::objectValue), response(Json::arrayValue);
			response[0U] = tank0;
			response[1U] = tank1;
			output["response"] = response;
			if (!debug.empty())
				output["debug"] = debug;
			if (!data.empty())
				output["data"] = data;
			if (!globaldata.empty())
				output["globaldata"] = globaldata;
			cout << writer.write(output) << endl;
		}
	}

	// �������������� cin ���� fstream����ȡ�غ���Ϣ������ TankField������ȡ�ϻغϴ洢�� data �� globaldata
	// ���ص��Ե�ʱ��֧�ֶ��У��������һ����Ҫ��û��������һ��"}"��"]"��β
	void ReadInput(istream& in, string& outData, string& outGlobalData)
	{
		Json::Value input;
		string inputString;
		do
		{
			getline(in, inputString);
		} while (inputString.empty());
#ifndef _BOTZONE_ONLINE
		// �²��ǵ��л��Ƕ���
		char lastChar = inputString[inputString.size() - 1];
		if (lastChar != '}' && lastChar != ']')
		{
			// ��һ�в���}��]��β���²��Ƕ���
			string newString;
			do
			{
				getline(in, newString);
				inputString += newString;
			} while (newString != "}" && newString != "]");
		}
#endif
		Internals::reader.parse(inputString, input);

		if (input.isObject())
		{
			Json::Value requests = input["requests"], responses = input["responses"];
			if (!requests.isNull() && requests.isArray())
			{
				size_t i, n = requests.size();
				for (i = 0; i < n; i++)
				{
					Internals::_processRequestOrResponse(requests[i], true);
					if (i < n - 1)
						Internals::_processRequestOrResponse(responses[i], false);
				}
				outData = input["data"].asString();
				outGlobalData = input["globaldata"].asString();
				return;
			}
		}
		Internals::_processRequestOrResponse(input, true);
	}

	// �ύ���߲��˳����»غ�ʱ���������г���
	void SubmitAndExit(Action tank0, Action tank1, string debug = "", string data = "", string globaldata = "")
	{
		Internals::_submitAction(tank0, tank1, debug, data, globaldata);
		exit(0);
	}

	// �ύ���ߣ��»غ�ʱ����������У���Ҫ�� Botzone ���ύ Bot ʱѡ������ʱ���С���
	// �����Ϸ����������ᱻϵͳɱ��
	void SubmitAndDontExit(Action tank0, Action tank1)
	{
		Internals::_submitAction(tank0, tank1);
		field->nextAction[field->mySide][0] = tank0;
		field->nextAction[field->mySide][1] = tank1;
		cout << ">>>BOTZONE_REQUEST_KEEP_RUNNING<<<" << endl;
	}
#ifdef _MSC_VER
#pragma endregion
#endif
}
class AlphaAndBeta
{
public:
	int alpha;
	int beta;
	AlphaAndBeta(int a = -100000000, int b = 100000000)
	{
		alpha = a;
		beta = b;
	}
};
class way {
public:
	way *father;
	int x;
	int y;
	int G;
	int H;
	int cate;//0 ʲô������  1����close 2����open
	way() {}
	way(int _x, int _y) :x(_x), y(_y) {
		G = H = 9999;
		cate = 0;
	}
	way(const way&r) :x(r.x), y(r.y), G(r.G), H(r.H), cate(r.cate) {}
	bool operator<(const way &r) {
		return (G + H) < (r.G + r.H);
	}
	bool operator==(const way &r) {
		if (x == r.x&&y == r.y&&G == r.G&&H == r.H&&cate == r.cate)
			return true;
		else
			return false;
	}
};
//int RandBetween(int from, int to)
//{
//	return rand() % (to - from) + from;
//}
using namespace TankGame;//�ӵ�
const int myside = 0;
const int opposide = 1;
//Ѱ·�㷨�����ؾ��루������

int min(way **p) {
	way *pp = p[0];
	int tmp = 0;
	for (int i = 1; i < 80; i++) {
		if (p[i] == nullptr&&*(p[i]) < *pp) {
			pp = p[i];
			tmp = i;
		}
	}
	return tmp;
}
bool find(way **p, way pp) {
	bool check = false;
	for (int i = 0; i < 80; i++) {
		if (p[i] == NULL)
			continue;
		if (*p[i] == pp)
			check = true;
	}
	return check;
}
int ways(int x, int y, int _x, int _y, TankField newfield) {
	way start(x, y);
	way end(_x, _y);
	int tmpx = x, tmpy = y;
	int endx = _x, endy = _y;
	way **open;
	open = new way*[80];
	memset(open, NULL, sizeof(open));
	way **close;
	close = new way*[80];
	memset(close, NULL, sizeof(close));
	way field[9][9];
	for (int i = 0; i < 9; i++)
		for (int j = 0; j < 9; j++)
			field[i][j] = way(i, j);
	field[x][y] = start;
	field[_x][_y] = end;
	int ic = 0, io = 0;
	close[ic] = new way(start);
	close[ic]->cate = 1;
	ic++;
	//������ʼλ��
	if (x == 0) {}
	else {
		if (newfield.gameField[x - 1][y] == None)
		{
			field[x - 1][y].cate = 2;
			field[x - 1][y].G += 10;
			field[x - 1][y].H = (abs(x - 1 - endx) + abs(y - endy)) * 10;
			field[x - 1][y].father = new way(start);
			open[io] = new way(field[x - 1][y]);
			io++;
		}
	}
	if (y == 0) {}
	else {
		if (newfield.gameField[x][y - 1] == None)
		{
			field[x][y - 1].cate = 2;
			field[x][y - 1].G += 10;
			field[x][y - 1].H = (abs(x - endx) + abs(y - 1 - endy)) * 10;
			field[x][y - 1].father = new way(start);
			open[io] = new way(field[x][y - 1]);
			io++;
		}
	}
	if (newfield.gameField[x][y + 1] == None)
	{
		field[x][y + 1].cate = 2;
		field[x][y + 1].G += 10;
		field[x][y + 1].H = (abs(x - endx) + abs(y + 1 - endy)) * 10;
		field[x][y + 1].father = new way(start);
		open[io] = new way(field[x][y + 1]);
		io++;
	}
	if (newfield.gameField[x + 1][y] == None)
	{
		field[x + 1][y].cate = 2;
		field[x + 1][y].G += 10;
		field[x + 1][y].H = (abs(x + 1 - endx) + abs(y - endy)) * 10;
		field[x + 1][y].father = new way(start);
		open[io] = new way(field[x + 1][y]);
		io++;
	}
	for (int i = 2;; i++) {
		int tmp = min(open);
		field[open[tmp]->x][open[tmp]->y].cate = 1;
		delete open[tmp];
		open[tmp] = NULL;
		close[ic] = new way(field[open[tmp]->x][open[tmp]->y]);
		ic++;
		tmpx = open[tmp]->x;
		tmpy = open[tmp]->y;
		if (tmpx == 0) {}
		else {
			if (newfield.gameField[tmpx - 1][tmpy] == None && field[tmpx - 1][tmpy].cate == 0)
			{
				field[tmpx - 1][tmpy].cate = 2;
				field[tmpx - 1][tmpy].G += 10 * i;
				field[tmpx - 1][tmpy].H = (abs(tmpx - 1 - endx) + abs(tmpy - endy)) * 10;
				field[tmpx - 1][tmpy].father = new way(field[tmpx - 1][tmpy]);
				open[io] = new way(field[tmpx - 1][tmpy]);
				io++;
			}
			else if (newfield.gameField[tmpx - 1][tmpy] == None && field[tmpx - 1][tmpy].cate == 2) {
				int tmpG = field[tmpx][tmpy].G + 10;
				int tmpH = (abs(tmpx - 1 - endx) + abs(tmpy - endy)) * 10;
				int tmpF = tmpH + tmpG;
				if (tmpF < (field[tmpx - 1][tmpy].H + field[tmpx - 1][tmpy].G)) {
					field[tmpx - 1][tmpy].G = tmpG;
					field[tmpx - 1][tmpy].H = tmpH;
					*field[tmpx - 1][tmpy].father = field[tmpx][tmpy];
				}
			}
		}
		if (tmpy == 0) {}
		else {
			if (newfield.gameField[tmpx][tmpy - 1] == None && field[tmpx][tmpy - 1].cate == 0)
			{
				field[tmpx][tmpy - 1].cate = 2;
				field[tmpx][tmpy - 1].G += 10 * i;
				field[tmpx][tmpy - 1].H = (abs(tmpx - endx) + abs(tmpy - 1 - endy)) * 10;
				field[tmpx][tmpy - 1].father = new way(field[tmpx][tmpy - 1]);
				open[io] = new way(field[tmpx][tmpy - 1]);
				io++;
			}
			else if (newfield.gameField[tmpx][tmpy - 1] == None && field[tmpx][tmpy - 1].cate == 2) {
				int tmpG = field[tmpx][tmpy - 1].G + 10;
				int tmpH = (abs(tmpx - endx) + abs(tmpy - 1 - endy)) * 10;
				int tmpF = tmpH + tmpG;
				if (tmpF < (field[tmpx][tmpy - 1].H + field[tmpx][tmpy - 1].G)) {
					field[tmpx][tmpy - 1].G = tmpG;
					field[tmpx][tmpy - 1].H = tmpH;
					*field[tmpx][tmpy - 1].father = field[tmpx][tmpy];
				}
			}
		}
		if (newfield.gameField[tmpx][tmpy + 1] == None && field[tmpx][tmpy + 1].cate == 0)
		{
			field[tmpx][tmpy + 1].cate = 2;
			field[tmpx][tmpy + 1].G += 10;
			field[tmpx][tmpy + 1].H = (abs(tmpx - endx) + abs(tmpy + 1 - endy)) * 10;
			field[tmpx][tmpy + 1].father = new way(field[tmpx][tmpy]);
			open[io] = new way(field[tmpx][tmpy + 1]);
			io++;
		}
		else if (newfield.gameField[tmpx][tmpy + 1] == None && field[tmpx][tmpy + 1].cate == 2) {
			int tmpG = field[tmpx][tmpy + 1].G + 10;
			int tmpH = (abs(tmpx - endx) + abs(tmpy + 1 - endy)) * 10;
			int tmpF = tmpH + tmpG;
			if (tmpF < (field[tmpx][tmpy + 1].H + field[tmpx][tmpy + 1].G)) {
				field[tmpx][tmpy + 1].G = tmpG;
				field[tmpx][tmpy + 1].H = tmpH;
				*field[tmpx][tmpy + 1].father = field[tmpx][tmpy];
			}
		}
		if (newfield.gameField[tmpx + 1][tmpy] == None && field[tmpx + 1][tmpy].cate == 0)
		{
			field[tmpx + 1][tmpy].cate = 2;
			field[tmpx + 1][tmpy].G += 10;
			field[tmpx + 1][tmpy].H = (abs(tmpx + 1 - endx) + abs(tmpy - endy)) * 10;
			field[tmpx + 1][tmpy].father = new way(field[tmpx][tmpy]);
			open[io] = new way(field[tmpx + 1][tmpy]);
			io++;
		}
		else if (newfield.gameField[tmpx + 1][tmpy] == None && field[tmpx + 1][tmpy].cate == 2) {
			int tmpG = field[tmpx][tmpy].G + 10;
			int tmpH = (abs(tmpx + 1 - endx) + abs(tmpy - endy)) * 10;
			int tmpF = tmpH + tmpG;
			if (tmpF < (field[tmpx + 1][tmpy].H + field[tmpx + 1][tmpy].G)) {
				field[tmpx + 1][tmpy].G = tmpG;
				field[tmpx + 1][tmpy].H = tmpH;
				*field[tmpx + 1][tmpy].father = field[tmpx][tmpy];
			}
		}
		if (find(open, end))
			break;
		if (i > 90)
			return 0;
	}
	int acc = 0;
	way tmp = field[endx][endy];
	while (true) {
		tmp = *tmp.father;
		acc++;
		if (tmp == start)
			break;
	}
	return acc;
}
//Ӯ�ĸ���
int Evaluation(TankGame::TankField newfield, int enermy) {
	int tmp = 0;
	//���ر���
	if (newfield.baseAlive[myside] == false && newfield.baseAlive[opposide] == true)
		return -6400;
	else if (newfield.baseAlive[myside] == true && newfield.baseAlive[opposide] == false)
		return 6400;
	else if (newfield.baseAlive[myside] == false && newfield.baseAlive[opposide] == false)
		return 6400;
	//tank����
	if (newfield.tankAlive[myside][0] == false && newfield.tankAlive[myside][1] == false &&
		(newfield.tankAlive[opposide][0] == true || newfield.tankAlive[opposide][1] == true))
		return -6400;
	else if (newfield.tankAlive[opposide][0] == false && newfield.tankAlive[opposide][1] == false &&
		(newfield.tankAlive[myside][0] == true || newfield.tankAlive[myside][1] == true))
		return 6400;
	else if (newfield.tankAlive[myside][0] == true && newfield.tankAlive[myside][1] == true &&
		newfield.tankAlive[opposide][0] == true && newfield.tankAlive[opposide][1] == true) {
		int my1, my2, oppo1, oppo2;//�ĸ�̹�˶Ը��ӵĿ���
		my1 = my2 = oppo1 = oppo2 = 0;
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				my1 += ways(newfield.tankX[0][0], newfield.tankY[0][0], i, j, newfield);
			}
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				my2 += ways(newfield.tankX[0][1], newfield.tankY[0][1], i, j, newfield);
			}
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				oppo1 += ways(newfield.tankX[1][0], newfield.tankY[1][0], i, j, newfield);
			}
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				oppo2 += ways(newfield.tankX[1][1], newfield.tankY[1][1], i, j, newfield);
			}
		return 6400 - (my1 + my2 - oppo1 - oppo2);
	}
	else if (newfield.tankAlive[myside][0] == true && newfield.tankAlive[myside][1] == true &&
		newfield.tankAlive[opposide][0] == true && newfield.tankAlive[opposide][1] == false) {
		int my1, my2, oppo1, oppo2;//����̹�˶Ը��ӵĿ���
		my1 = my2 = oppo1 = oppo2 = 0;
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				my1 += ways(newfield.tankX[0][0], newfield.tankY[0][0], i, j, newfield);
			}
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				my2 += ways(newfield.tankX[0][1], newfield.tankY[0][1], i, j, newfield);
			}
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				oppo1 += ways(newfield.tankX[1][0], newfield.tankY[1][0], i, j, newfield);
			}
		return 6400 - (my1 + my2 - oppo1 - oppo2);
	}
	else if (newfield.tankAlive[myside][0] == true && newfield.tankAlive[myside][1] == true &&
		newfield.tankAlive[opposide][0] == false && newfield.tankAlive[opposide][1] == true) {
		int my1, my2, oppo1, oppo2;//����̹�˶Ը��ӵĿ���
		my1 = my2 = oppo1 = oppo2 = 0;
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				my1 += ways(newfield.tankX[0][0], newfield.tankY[0][0], i, j, newfield);
			}
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				my2 += ways(newfield.tankX[0][1], newfield.tankY[0][1], i, j, newfield);
			}
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				oppo2 += ways(newfield.tankX[1][1], newfield.tankY[1][1], i, j, newfield);
			}
		return 6400 - (my1 + my2 - oppo1 - oppo2);
	}
	else if (newfield.tankAlive[myside][0] == true && newfield.tankAlive[myside][1] == false &&
		newfield.tankAlive[opposide][0] == true && newfield.tankAlive[opposide][1] == true) {
		int my1, my2, oppo1, oppo2;//����̹�˶Ը��ӵĿ���
		my1 = my2 = oppo1 = oppo2 = 0;
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				my1 += ways(newfield.tankX[0][0], newfield.tankY[0][0], i, j, newfield);
			}
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				oppo1 += ways(newfield.tankX[1][0], newfield.tankY[1][0], i, j, newfield);
			}
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				oppo2 += ways(newfield.tankX[1][1], newfield.tankY[1][1], i, j, newfield);
			}
		return 6400 - (my1 + my2 - oppo1 - oppo2);
	}
	else if (newfield.tankAlive[myside][0] == false && newfield.tankAlive[myside][1] == true &&
		newfield.tankAlive[opposide][0] == true && newfield.tankAlive[opposide][1] == true) {
		int my1, my2, oppo1, oppo2;//����̹�˶Ը��ӵĿ���
		my1 = my2 = oppo1 = oppo2 = 0;
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				my2 += ways(newfield.tankX[0][1], newfield.tankY[0][1], i, j, newfield);
			}
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				oppo1 += ways(newfield.tankX[1][0], newfield.tankY[1][0], i, j, newfield);
			}
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				oppo2 += ways(newfield.tankX[1][1], newfield.tankY[1][1], i, j, newfield);
			}
		return 6400 - (my1 + my2 - oppo1 - oppo2);
	}
	else if (newfield.tankAlive[myside][0] == true && newfield.tankAlive[myside][1] == false &&
		newfield.tankAlive[opposide][0] == true && newfield.tankAlive[opposide][1] == false) {
		int my1, my2, oppo1, oppo2;//2��̹�˶Ը��ӵĿ���
		my1 = my2 = oppo1 = oppo2 = 0;
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				my1 += ways(newfield.tankX[0][0], newfield.tankY[0][0], i, j, newfield);
			}
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				oppo1 += ways(newfield.tankX[1][0], newfield.tankY[1][0], i, j, newfield);
			}
		return 6400 - (my1 + my2 - oppo1 - oppo2);
	}
	else if (newfield.tankAlive[myside][0] == true && newfield.tankAlive[myside][1] == false &&
		newfield.tankAlive[opposide][0] == false && newfield.tankAlive[opposide][1] == true) {
		int my1, my2, oppo1, oppo2;//�ĸ�̹�˶Ը��ӵĿ���
		my1 = my2 = oppo1 = oppo2 = 0;
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				my1 += ways(newfield.tankX[0][0], newfield.tankY[0][0], i, j, newfield);
			}
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				oppo2 += ways(newfield.tankX[1][1], newfield.tankY[1][1], i, j, newfield);
			}
		return 6400 - (my1 + my2 - oppo1 - oppo2);
	}
	else if (newfield.tankAlive[myside][0] == false && newfield.tankAlive[myside][1] == true &&
		newfield.tankAlive[opposide][0] == false && newfield.tankAlive[opposide][1] == true) {
		int my1, my2, oppo1, oppo2;//�ĸ�̹�˶Ը��ӵĿ���
		my1 = my2 = oppo1 = oppo2 = 0;
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				my2 += ways(newfield.tankX[0][1], newfield.tankY[0][1], i, j, newfield);
			}
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				oppo2 += ways(newfield.tankX[1][1], newfield.tankY[1][1], i, j, newfield);
			}
		return 6400 - (my1 + my2 - oppo1 - oppo2);
	}
	else if (newfield.tankAlive[myside][0] == false && newfield.tankAlive[myside][1] == true &&
		newfield.tankAlive[opposide][0] == true && newfield.tankAlive[opposide][1] == false) {
		int my1, my2, oppo1, oppo2;//�ĸ�̹�˶Ը��ӵĿ���
		my1 = my2 = oppo1 = oppo2 = 0;
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				my2 += ways(newfield.tankX[0][1], newfield.tankY[0][1], i, j, newfield);
			}
		for (int i = 0; i < 9; i++)
			for (int j = 0; j < 9; j++) {
				oppo1 += ways(newfield.tankX[1][0], newfield.tankY[1][0], i, j, newfield);
			}
		return 6400 - (my1 + my2 - oppo1 - oppo2);
	}
}
int RandEvaluation(TankField field, bool minORmax)
{
	if (field.baseAlive[field.mySide] == 0)
	{
		return -10000001;
	}
	else
	{
		int a = 0;
		a = 192 - pow(field.tankX[field.mySide][0] - baseY[1 - field.mySide], 2)
			- pow(field.tankY[field.mySide][0] - baseY[1 - field.mySide], 2)
			- pow(field.tankX[field.mySide][1] - baseY[1 - field.mySide], 2)
			- pow(field.tankY[field.mySide][1] - baseY[1 - field.mySide], 2);
		return a;
	}
}
Action bestaction[1][2];
clock_t start = clock();
AlphaAndBeta search(TankField &newfield, int myside, int side, int no = 0)
{
	if (clock() - start < 0.8 * CLOCKS_PER_SEC)
	{
		AlphaAndBeta record;
		bool cut = 0;
		if (no == 3)//��3��
		{
				record.alpha = RandEvaluation(newfield, 1);
				return record;
		}
		else
		{
			for (int i = -2; i <= 7; i++)//0��tank
			{
				if (newfield.tankAlive[side][0]&& newfield.ActionIsValid(side, 0, (Action)i))
				{
						newfield.nextAction[side][0] = (Action)i;
				}
				else if(newfield.tankAlive[side][0] && !newfield.ActionIsValid(side, 0, (Action)i))
				{
					continue;
				}
				for (int j = -2; j <= 7; j++)//1��tank
				{
					if (newfield.tankAlive[side][1]&& newfield.ActionIsValid(side, 1, (Action)j))
					{
							newfield.nextAction[side][1] = (Action)j;
					}
					else if(newfield.tankAlive[side][1] && !newfield.ActionIsValid(side, 1, (Action)j))
					{
						continue;
					}
					if (side == myside)
					{
						if (cut == 0)
						{
							auto x = search(newfield, myside, 1-side,no+1);
							if (no == 0)
							{
								if (record.alpha < x.beta)
								{
									record.alpha = x.beta;
									bestaction[0][0] = field->previousActions[field->currentTurn][field->mySide][0];
									bestaction[0][1] = field->previousActions[field->currentTurn][field->mySide][1];
								}
							}
							if (record.alpha < x.beta)
							{
								record.alpha = x.beta;
							}
							else
							{
								cut = 0;
								break;
							}
						}
						return record;
					}
					else//һ���غϽ���
					{
						newfield.DoAction();
						auto x = search(newfield, myside, 1-side,no+1);
						newfield.Revert();
						if (record.beta > x.alpha)
						{
							record.beta = x.alpha;
						}
						return record;
					}
				}
			}

		}
	}
	else//������ʱ
	{
		TankGame::SubmitAndExit(bestaction[0][0], bestaction[1][1]);
	}
}




	//TankGame::Action RandAction(int tank)
	//{
	//	while (true)
	//	{
	//		auto act = (TankGame::Action)RandBetween(TankGame::Stay, TankGame::LeftShoot + 1);
	//		if (TankGame::field->ActionIsValid(TankGame::field->mySide, tank, act))
	//			return act;
	//	}
	//}

int main()
{
	srand((unsigned)time(nullptr));
	string data, globaldata;
	TankGame::ReadInput(cin, data, globaldata);
	search(*field, field->mySide, field->mySide);
	//Action previousActions[101][sideCount][tankPerSide] = { { { Stay, Stay },{ Stay, Stay } } };
	TankGame::SubmitAndExit(bestaction[0][0], bestaction[0][1]);
}