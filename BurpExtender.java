package burp;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Component;
import java.awt.Font;
import java.awt.GridLayout;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.lang.reflect.Method;
import java.net.URI;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JLabel;
import javax.swing.JMenuItem;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JSplitPane;
import javax.swing.JTabbedPane;
import javax.swing.JTable;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.SwingUtilities;
import javax.swing.table.AbstractTableModel;
import javax.swing.table.DefaultTableCellRenderer;
import javax.swing.table.TableModel;

import burp.api.montoya.BurpExtension;
import burp.api.montoya.MontoyaApi;
import burp.api.montoya.core.ToolType;
import burp.api.montoya.http.Http;
import burp.api.montoya.http.handler.HttpHandler;
import burp.api.montoya.http.handler.HttpRequestToBeSent;
import burp.api.montoya.http.handler.HttpResponseReceived;
import burp.api.montoya.http.handler.RequestToBeSentAction;
import burp.api.montoya.http.handler.ResponseReceivedAction;
import burp.api.montoya.http.message.HttpRequestResponse;
import burp.api.montoya.http.message.params.HttpParameter;
import burp.api.montoya.http.message.params.HttpParameterType;
import burp.api.montoya.http.message.params.ParsedHttpParameter;
import burp.api.montoya.http.message.requests.HttpRequest;
import burp.api.montoya.http.message.responses.HttpResponse;
import burp.api.montoya.ui.UserInterface;
import burp.api.montoya.ui.contextmenu.ContextMenuEvent;
import burp.api.montoya.ui.contextmenu.ContextMenuItemsProvider;
import burp.api.montoya.ui.editor.HttpRequestEditor;
import burp.api.montoya.ui.editor.HttpResponseEditor;

public class BurpExtender implements BurpExtension {

    private MontoyaApi api;
    private Http http;
    private UserInterface ui;

    private PrintWriter stdout;
    private JSplitPane splitPane;
    private HttpRequestEditor requestViewer;
    private HttpResponseEditor responseViewer;

    private final List<LogEntry>   log     = Collections.synchronizedList(new ArrayList<>());
    private final List<LogEntry>   log2    = Collections.synchronizedList(new ArrayList<>());
    private final List<LogEntry>   log3    = Collections.synchronizedList(new ArrayList<>());
    private final List<RequestMd5> log4Md5 = Collections.synchronizedList(new ArrayList<>());

    // ── 基础开关 ──────────────────────────────────────────────
    private int    switchs        = 1;
    private int    clicksRepeater = 0;
    private int    clicksProxy    = 0;
    private final AtomicInteger count      = new AtomicInteger(0);
    private volatile String dataMd5Id;
    private int    isInt          = 1;
    private int    jTextAreaInt   = 0;
    private String jTextAreaData1 = "";
    private int    diyPayload1    = 1;
    private int    diyPayload2    = 0;
    private Table  logTable;
    private int    isCookie       = -1;
    private String whiteUrl       = "*";
    private int    whiteSwitchs   = 0;
    private volatile int requestIntervalMs = 0;
    private final AtomicLong lastSendAt = new AtomicLong(0);
    private final Object sendLock = new Object();
    private static final int MAX_REQUESTS_PER_PARAM = 18;
    private static final long SINGLE_REQUEST_SLOW_MS = 4000;
    private final AtomicInteger detailRefreshPending = new AtomicInteger(0);

    // ── 自定义报错信息 ────────────────────────────────────────
    private static final String DEFAULT_ERROR_PATTERNS =
            "ORA-\\d{5}\n" +
                    "SQL syntax.*?MySQL\n" +
                    "Unknown column\n" +
                    "SQL syntax\n" +
                    "java.sql.SQLSyntaxErrorException\n" +
                    "Error SQL:\n" +
                    "Syntax error\n" +
                    "附近有语法错误\n" +
                    "java.sql.SQLException\n" +
                    "引号不完整\n" +
                    "System.Exception: SQL Execution Error!\n" +
                    "com.mysql.jdbc\n" +
                    "MySQLSyntaxErrorException\n" +
                    "valid MySQL result\n" +
                    "your MySQL server version\n" +
                    "MySqlClient\n" +
                    "MySqlException\n" +
                    "valid PostgreSQL result\n" +
                    "PG::SyntaxError:\n" +
                    "org.postgresql.jdbc\n" +
                    "PSQLException\n" +
                    "Microsoft SQL Native Client error\n" +
                    "ODBC SQL Server Driver\n" +
                    "SQLServer JDBC Driver\n" +
                    "com.jnetdirect.jsql\n" +
                    "macromedia.jdbc.sqlserver\n" +
                    "com.microsoft.sqlserver.jdbc\n" +
                    "Microsoft Access\n" +
                    "Access Database Engine\n" +
                    "ODBC Microsoft Access\n" +
                    "Oracle error\n" +
                    "DB2 SQL error\n" +
                    "SQLite error\n" +
                    "Sybase message\n" +
                    "SybSQLException";

    private String diyErrorText = DEFAULT_ERROR_PATTERNS;
    private volatile List<Pattern> compiledErrorPatterns = Collections.emptyList();

    // ── 日志面板 ─────────────────────────────────────────────
    private JTextArea logTextArea;

    public MyModel model = new MyModel();

    // =========================================================
    // initialize
    // =========================================================
    @Override
    public void initialize(MontoyaApi api) {
        this.api  = api;
        this.http = api.http();
        this.ui   = api.userInterface();

        stdout = new PrintWriter(new OutputStream() {
            @Override public void write(int b) {}
            @Override
            public void write(byte[] b, int off, int len) {
                api.logging().logToOutput(new String(b, off, len, StandardCharsets.UTF_8));
            }
        }, true);

        stdout.println("hello xia sql!");
        stdout.println("你好 欢迎使用 瞎注-子夜!");
        stdout.println("version:1.0");
        api.extension().setName("xia SQL V1.0+");
        refreshCompiledErrorPatterns();

        // HTTP 流量监听
        http.registerHttpHandler(new HttpHandler() {
            @Override
            public RequestToBeSentAction handleHttpRequestToBeSent(HttpRequestToBeSent request) {
                return RequestToBeSentAction.continueWith(request);
            }

            @Override
            public ResponseReceivedAction handleHttpResponseReceived(HttpResponseReceived response) {
                if (switchs != 1) return ResponseReceivedAction.continueWith(response);
                boolean fromRepeater = response.toolSource().isFromTool(ToolType.REPEATER);
                boolean fromProxy    = response.toolSource().isFromTool(ToolType.PROXY);
                if ((clicksRepeater == 1 && fromRepeater) || (clicksProxy == 1 && fromProxy)) {
                    HttpRequest         req = response.initiatingRequest();
                    HttpResponse        res = response;
                    HttpRequestResponse hrr = HttpRequestResponse.httpRequestResponse(req, res);
                    new Thread(() -> {
                        try { checkVul(hrr, 0); }
                        catch (Exception ex) { ex.printStackTrace(stdout); }
                    }).start();
                }
                return ResponseReceivedAction.continueWith(response);
            }
        });

        // 右键菜单
        ui.registerContextMenuItemsProvider(new ContextMenuItemsProvider() {
            @Override
            public List<Component> provideMenuItems(ContextMenuEvent event) {
                List<Component> items = new ArrayList<>();
                List<HttpRequestResponse> messages = event.selectedRequestResponses();
                if (messages.isEmpty()) return items;
                JMenuItem item = new JMenuItem("Send to xia SQL");
                item.addActionListener(e -> {
                    if (switchs != 1) { stdout.println("插件xia SQL关闭状态！"); return; }
                    new Thread(() -> {
                        try { checkVul(messages.get(0), 1024); }
                        catch (Exception ex) { ex.printStackTrace(stdout); }
                    }).start();
                });
                items.add(item);
                return items;
            }
        });

        SwingUtilities.invokeLater(this::buildUi);
    }

    // =========================================================
    // 构建 UI
    // =========================================================
    private void buildUi() {
        splitPane = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);

        // ── 大左侧：上部(主表+结果表左右并排) / 下部(请求响应) ──
        JSplitPane bigLeftPanel = new JSplitPane(JSplitPane.VERTICAL_SPLIT);

        // 上部：主表(左) + 结果表(右) 水平并排
        JSplitPane tablesSplit = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT);

        logTable = new Table(BurpExtender.this);
        JPanel logPanel = new JPanel(new GridLayout(1, 1));
        JScrollPane logScrollPane = new JScrollPane(logTable);
        logPanel.add(logScrollPane);

        TableLog2 table2 = new TableLog2(model);
        JPanel resultPanel = new JPanel(new BorderLayout());
        JLabel resultLabel = new JLabel("  SQL Injection Results (详细结果)");
        resultLabel.setOpaque(true);
        resultLabel.setBackground(new Color(230, 230, 230));
        resultLabel.setFont(new Font("Dialog", Font.BOLD, 14));
        JScrollPane resultScrollPane = new JScrollPane(table2);
        resultPanel.setBorder(null);
        resultScrollPane.setBorder(logScrollPane.getBorder());
        resultScrollPane.setViewportBorder(logScrollPane.getViewportBorder());
        resultPanel.add(resultLabel, BorderLayout.NORTH);
        resultPanel.add(resultScrollPane, BorderLayout.CENTER);

        tablesSplit.setLeftComponent(logPanel);
        tablesSplit.setRightComponent(resultPanel);
        tablesSplit.setResizeWeight(0.5);
        tablesSplit.setDividerLocation(480);

        // 下部：请求/响应
        JTabbedPane reqRespTabs = new JTabbedPane();
        requestViewer  = ui.createHttpRequestEditor();
        responseViewer = ui.createHttpResponseEditor();
        reqRespTabs.addTab("Request",  requestViewer.uiComponent());
        reqRespTabs.addTab("Response", responseViewer.uiComponent());

        bigLeftPanel.setTopComponent(tablesSplit);
        bigLeftPanel.setBottomComponent(reqRespTabs);
        bigLeftPanel.setResizeWeight(0.5);
        bigLeftPanel.setDividerLocation(400);

        // ── 右侧控制面板 ────────────────────────────────────
        JSplitPane rightPanel = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
        JPanel ctrlPanel = new JPanel(new GridLayout(16, 1));
        ctrlPanel.add(new JLabel("插件名：瞎注 author：子夜"));
        ctrlPanel.add(new JLabel("blog:sunwu.world"));
        ctrlPanel.add(new JLabel("版本：xia SQL V3.3二开版本"));
        ctrlPanel.add(new JLabel("感谢名单：算命瞎子"));

        JCheckBox chkbox1 = new JCheckBox("启动插件", true);
        JCheckBox chkbox2 = new JCheckBox("监控Repeater");
        JCheckBox chkbox3 = new JCheckBox("监控Proxy");
        JCheckBox chkbox4 = new JCheckBox("值是数字则进行-1、-0", true);
        JCheckBox chkbox8 = new JCheckBox("测试Cookie");
        JTextField textField = new JTextField("*");
        JTextField intervalField = new JTextField("发包间隔毫秒(默认0)");
        JButton btn1 = new JButton("清空列表");
        JButton btn3 = new JButton("启动白名单");
        JButton btnInterval = new JButton("设置发包间隔");

        ctrlPanel.add(chkbox1);
        ctrlPanel.add(chkbox2);
        ctrlPanel.add(chkbox3);
        ctrlPanel.add(chkbox4);
        ctrlPanel.add(chkbox8);
        ctrlPanel.add(new JLabel("全局发包间隔(毫秒)"));
        ctrlPanel.add(intervalField);
        ctrlPanel.add(btnInterval);
        ctrlPanel.add(btn1);
        ctrlPanel.add(new JLabel("白名单目标支持逗号分隔，例如 *.baidu.com"));
        ctrlPanel.add(textField);
        ctrlPanel.add(btn3);

        // ── 右侧 Tab ────────────────────────────────────────
        JTabbedPane tabDiy = new JTabbedPane();

        // Tab1：自定义 payload
        JPanel yx1Panel = new JPanel(new BorderLayout());
        JPanel yx1Top   = new JPanel(new GridLayout(5, 1));
        JCheckBox chkbox5 = new JCheckBox("自定义payload");
        JCheckBox chkbox6 = new JCheckBox("自定义payload中空格url编码", true);
        JCheckBox chkbox7 = new JCheckBox("自定义payload中参数值置空");
        JButton   btn2    = new JButton("加载/重新加载payload");
        yx1Top.add(new JLabel("修改payload后记得点击加载"));
        yx1Top.add(chkbox5);
        yx1Top.add(chkbox6);
        yx1Top.add(chkbox7);
        yx1Top.add(btn2);

        JTextArea jta = new JTextArea("%df' and sleep(3)%23\n'and '1'='1", 18, 16);
        try (BufferedReader in = new BufferedReader(new FileReader("xia_SQL_diy_payload.ini"))) {
            StringBuilder sb = new StringBuilder();
            String line;
            while ((line = in.readLine()) != null) sb.append(line).append("\n");
            jta.setText(sb.toString());
        } catch (IOException ignored) {}
        jta.setForeground(Color.BLACK);
        jta.setFont(new Font("楷体", Font.BOLD, 16));
        jta.setBackground(Color.LIGHT_GRAY);
        jta.setEditable(false);
        yx1Panel.add(yx1Top, BorderLayout.NORTH);
        yx1Panel.add(new JScrollPane(jta), BorderLayout.CENTER);
        tabDiy.addTab("自定义SQL语句", yx1Panel);

        // Tab2：自定义报错信息
        JSplitPane yx2Sp = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
        JPanel yx2Top = new JPanel();
        JCheckBox chkboxDiyError = new JCheckBox("启用自定义报错信息（支持正则表达式）", true);
        yx2Top.add(chkboxDiyError);
        JTextArea diyErrorJta = new JTextArea(DEFAULT_ERROR_PATTERNS, 18, 24);
        diyErrorJta.setEditable(false);
        diyErrorJta.setBackground(Color.LIGHT_GRAY);
        diyErrorJta.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 13));
        diyErrorText = diyErrorJta.getText();
        JPanel yx2Bottom = new JPanel(new GridLayout(1, 1));
        yx2Bottom.add(new JScrollPane(diyErrorJta));
        yx2Sp.setTopComponent(yx2Top);
        yx2Sp.setBottomComponent(yx2Bottom);
        yx2Sp.setResizeWeight(0.15);
        tabDiy.addTab("自定义报错信息", yx2Sp);

        // Tab3：日志
        JSplitPane yx3Sp = new JSplitPane(JSplitPane.VERTICAL_SPLIT);
        JPanel yx3Top = new JPanel();
        JButton logBtn = new JButton("清空日志");
        yx3Top.add(logBtn);
        logTextArea = new JTextArea("");
        logTextArea.setEditable(false);
        logTextArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));
        JPanel yx3Bottom = new JPanel(new GridLayout(1, 1));
        yx3Bottom.add(new JScrollPane(logTextArea));
        yx3Sp.setTopComponent(yx3Top);
        yx3Sp.setBottomComponent(yx3Bottom);
        yx3Sp.setResizeWeight(0.1);
        tabDiy.addTab("日志", yx3Sp);

        rightPanel.setTopComponent(ctrlPanel);
        rightPanel.setBottomComponent(tabDiy);

        splitPane.setLeftComponent(bigLeftPanel);
        splitPane.setRightComponent(rightPanel);
        splitPane.setDividerLocation(1000);

        // ── 事件绑定 ─────────────────────────────────────────
        chkbox1.addItemListener(e -> {
            switchs = chkbox1.isSelected() ? 1 : 0;
            stdout.println(chkbox1.isSelected() ? "插件xia SQL启动" : "插件xia SQL关闭");
        });
        chkbox2.addItemListener(e -> {
            clicksRepeater = chkbox2.isSelected() ? 1 : 0;
            stdout.println((chkbox2.isSelected() ? "启动" : "关闭") + " 监控Repeater");
        });
        chkbox3.addItemListener(e -> {
            clicksProxy = chkbox3.isSelected() ? 1 : 0;
            stdout.println((chkbox3.isSelected() ? "启动" : "关闭") + " 监控Proxy");
        });
        chkbox4.addItemListener(e -> {
            isInt = chkbox4.isSelected() ? 1 : 0;
            stdout.println((chkbox4.isSelected() ? "启动" : "关闭") + " 值是数字则进行-1、-0");
        });
        chkbox5.addItemListener(e -> {
            if (chkbox5.isSelected()) {
                jta.setEditable(true);
                jta.setBackground(Color.WHITE);
                jTextAreaInt   = 1;
                jTextAreaData1 = (diyPayload1 == 1) ? jta.getText().replace(" ", "%20") : jta.getText();
                stdout.println("启动 自定义payload");
            } else {
                jta.setEditable(false);
                jta.setBackground(Color.LIGHT_GRAY);
                jTextAreaInt = 0;
                stdout.println("关闭 自定义payload");
            }
        });
        chkbox6.addItemListener(e -> {
            if (chkbox6.isSelected()) {
                diyPayload1    = 1;
                jTextAreaData1 = jta.getText().replace(" ", "%20");
                stdout.println("启动 空格url编码");
            } else {
                diyPayload1    = 0;
                jTextAreaData1 = jta.getText();
                stdout.println("关闭 空格url编码");
            }
        });
        chkbox7.addItemListener(e -> {
            diyPayload2 = chkbox7.isSelected() ? 1 : 0;
            stdout.println((chkbox7.isSelected() ? "启动" : "关闭") + " 自定义payload参数值置空");
        });
        chkbox8.addItemListener(e -> {
            isCookie = chkbox8.isSelected() ? 2 : -1;
            stdout.println((chkbox8.isSelected() ? "启动" : "关闭") + " 测试Cookie");
        });
        chkboxDiyError.addItemListener(e -> {
            if (chkboxDiyError.isSelected()) {
                diyErrorText = diyErrorJta.getText();
                refreshCompiledErrorPatterns();
                diyErrorJta.setEditable(false);
                diyErrorJta.setBackground(Color.LIGHT_GRAY);
                stdout.println("启用 自定义报错信息");
            } else {
                diyErrorJta.setEditable(true);
                diyErrorJta.setBackground(Color.WHITE);
                diyErrorText = DEFAULT_ERROR_PATTERNS;
                refreshCompiledErrorPatterns();
                stdout.println("关闭 自定义报错信息（保留默认规则）");
            }
        });
        btn1.addActionListener(e -> {
            log.clear(); log2.clear(); log3.clear(); log4Md5.clear();
            count.set(0);
            fireTableDataChanged();
            model.fireTableDataChanged();
        });
        btn2.addActionListener(e -> {
            jTextAreaData1 = (diyPayload1 == 1) ? jta.getText().replace(" ", "%20") : jta.getText();
            try (BufferedWriter out = new BufferedWriter(new FileWriter("xia_SQL_diy_payload.ini"))) {
                out.write(jTextAreaData1);
            } catch (IOException ignored) {}
            stdout.println("payload 已加载");
        });
        textField.setEditable(true);
        textField.setForeground(Color.BLACK);
        btn3.addActionListener(e -> {
            if (btn3.getText().equals("启动白名单")) {
                btn3.setText("关闭白名单");
                whiteUrl = textField.getText() == null ? "*" : textField.getText().trim();
                if (whiteUrl.isEmpty()) whiteUrl = "*";
                whiteSwitchs = 1;
                textField.setEditable(false);
                textField.setForeground(Color.GRAY);
                stdout.println("已启用白名单: " + whiteUrl);
            } else {
                btn3.setText("启动白名单");
                whiteSwitchs = 0;
                textField.setEditable(true);
                textField.setForeground(Color.BLACK);
                stdout.println("已关闭白名单");
            }
        });
        btnInterval.addActionListener(e -> {
            String text = intervalField.getText() == null ? "" : intervalField.getText().trim();
            int value;
            try {
                value = Integer.parseInt(text);
            } catch (Exception ex) {
                stdout.println("发包间隔设置失败：请输入非负整数");
                return;
            }
            if (value < 0) {
                stdout.println("发包间隔设置失败：请输入非负整数");
                return;
            }
            requestIntervalMs = value;
            stdout.println("发包间隔已设置为 " + requestIntervalMs + " ms");
        });
        logBtn.addActionListener(e -> logTextArea.setText(""));

        api.userInterface().registerSuiteTab("xia SQL", splitPane);
    }

    // =========================================================
    // 漏洞检测核心逻辑
    // =========================================================
    private void checkVul(HttpRequestResponse baseRequestResponse, int toolFlag) {
        int    isAdd       = 0;
        String changeSign1 = "";

        HttpRequest  req  = baseRequestResponse.request();
        HttpResponse resp = baseRequestResponse.response();
        String scanId = "RID-" + System.nanoTime();
        String requestHost = extractHost(req.url().toString());

        List<ParsedHttpParameter> paraLists = req.parameters();
        String requestBase = req.url().toString().split("\\?")[0];

        // 白名单过滤
        if (whiteSwitchs == 1) {
            if (!isWhitelistedHost(requestHost, whiteUrl)) {
                appendLog("不是白名单目标 host=" + requestHost + " url=" + requestBase);
                return;
            }
        }

        // 静态文件过滤
        if (toolFlag != 1024) {
            String[] staticFiles = {"jpg","png","gif","css","js","pdf","mp3","mp4","avi"};
            String[] parts = requestBase.split("\\.");
            String ext = parts[parts.length - 1].toLowerCase();
            for (String s : staticFiles) {
                if (ext.equals(s)) { appendLog("静态文件跳过：" + requestBase); return; }
            }
        }

        // 构建 MD5 去重 key
        for (ParsedHttpParameter para : paraLists) {
            HttpParameterType type = para.type();
            if (type == HttpParameterType.URL || type == HttpParameterType.BODY ||
                    type == HttpParameterType.JSON ||
                    (isCookie == 2 && type == HttpParameterType.COOKIE)) {
                isAdd = 1;
                requestBase += "+" + para.name();
            }
        }
        requestBase += "+" + req.method();
        String requestMd5 = md5(requestBase);

        synchronized (log4Md5) {
            for (RequestMd5 i : log4Md5) {
                if (i.md5Data.equals(requestMd5) && toolFlag != 1024) return;
            }
        }
        if (isAdd == 0) return;

        synchronized (log4Md5) {
            log4Md5.add(new RequestMd5(requestMd5));
        }

        if (resp == null || resp.statusCode() < 200 || resp.statusCode() >= 300) {
            appendLog(scanId + " 无响应或响应非2xx：" + req.url());
            return;
        }

        appendLog(scanId + " 开始检测 URL=" + req.url() + " 方法=" + req.method());

        // 添加主表占位行
        synchronized (log) {
            int row = log.size();
            log.add(new LogEntry(count.getAndIncrement(), toolFlag, baseRequestResponse,
                    req.url().toString(), "", "", "", requestMd5, 0, "run……", 999, false));
            SwingUtilities.invokeLater(() -> {
                fireTableRowsInserted(row, row);
                if (logTable != null && logTable.getSelectedRow() < 0) {
                    logTable.setRowSelectionInterval(row, row);
                }
            });
        }

        int baseRespLen = resp.body().length();
        boolean anyVulnFound = false;

        for (ParsedHttpParameter para : req.parameters()) {
            HttpParameterType type = para.type();
            boolean valid = (type == HttpParameterType.URL || type == HttpParameterType.BODY ||
                    type == HttpParameterType.JSON ||
                    (isCookie == 2 && type == HttpParameterType.COOKIE));
            if (!valid) continue;

            String key   = para.name();
            String value = para.value();
            appendLog(scanId + " 测试参数：url=" + req.url() + " param=" + key + " value=" + value);
            int sentRequests = 0;
            boolean slowDetected = false;
            long quickBaselineCost = Long.MAX_VALUE;
            List<LogEntry> paramEntries = new ArrayList<>();
            List<LogEntry> quoteEntries = new ArrayList<>();
            List<LogEntry> numEntries = new ArrayList<>();
            List<LogEntry> commaEntries = new ArrayList<>();
            List<LogEntry> expEntries = new ArrayList<>();
            List<LogEntry> divEntries = new ArrayList<>();
            List<LogEntry> sleepEntries = new ArrayList<>();
            List<LogEntry> diyEntries = new ArrayList<>();

            // ================================================================
            // 新注入判断逻辑：发送 1~4 个单引号，根据响应长度规律判断注入
            //
            // 规则：
            //   设 len1=len('), len2=len(''), len3=len('''), len4=len('''')
            //   满足以下三个条件即判定为 SQL 注入：
            //     ① |len2 - len4| <= 5   （偶数引号长度相近）
            //     ② |len1 - len3| <= 5   （奇数引号长度相近）
            //     ③ |len1 - len2| > 5    （奇偶引号长度差异明显）
            // ================================================================

            // 发送四个基础 payload 并收集响应长度
            int[] quoteLens = new int[4]; // 下标 0=', 1='', 2=''', 3=''''
            HttpRequestResponse[] quoteResults = new HttpRequestResponse[4];
            String[] quotePayloads = {"'", "''", "'''", "''''"};

            for (int qi = 0; qi < 4; qi++) {
                if (sentRequests >= MAX_REQUESTS_PER_PARAM) {
                    appendLog(scanId + " 参数=" + key + " 达到最大测试请求数，停止后续payload");
                    break;
                }
                HttpRequest qReq = buildMutatedRequest(req, para, value + quotePayloads[qi]);
                long t1 = System.currentTimeMillis();
                HttpRequestResponse qResult = sendRequestWithInterval(qReq);
                long cost = System.currentTimeMillis() - t1;
                sentRequests++;
                if (cost > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                quoteResults[qi] = qResult;
                HttpResponse qResp = qResult.response();
                boolean qOk = (qResp != null && qResp.statusCode() >= 200 && qResp.statusCode() < 300);
                if (qOk && cost < quickBaselineCost) quickBaselineCost = cost;
                quoteLens[qi] = qOk ? qResp.body().length() : 0;

                // 记录到详情表
                int code = qOk ? qResp.statusCode() : 0;
                HttpRequestResponse qDisplay = buildDisplayMessage(qReq, qResult);
                LogEntry detail = addDetailEntry(new LogEntry(count.get(), toolFlag, qDisplay,
                        qReq.url().toString(),
                        key, value + quotePayloads[qi], "", requestMd5, (int) cost, "end", code, false));
                paramEntries.add(detail);
                quoteEntries.add(detail);
            }

            int len1 = quoteLens[0]; // '
            int len2 = quoteLens[1]; // ''
            int len3 = quoteLens[2]; // '''
            int len4 = quoteLens[3]; // ''''

            appendLog(String.format("  引号测试 [%s] len('=%d, ''=%d, '''=%d, ''''=%d)",
                    key, len1, len2, len3, len4));

            boolean cond1 = Math.abs(len2 - len4) <= 5; // 偶数引号长度相近
            boolean cond2 = Math.abs(len1 - len3) <= 5; // 奇数引号长度相近
            boolean cond3 = Math.abs(len1 - len2) > 5;  // 奇偶引号长度差异明显

            boolean quoteVuln = cond1 && cond2 && cond3;

            // 数字参数检测：-0 / -0-0 / -0-1
            boolean numVuln = false;
            if (isInt == 1 && value.matches("^-?\\d+(\\.\\d+)?$")) {
                String[] numPayloads = {"-0", "-0-0", "-0-1"};
                int[] numLens = new int[3];

                for (int ni = 0; ni < 3; ni++) {
                    if (sentRequests >= MAX_REQUESTS_PER_PARAM) {
                        appendLog(scanId + " 参数=" + key + " 达到最大测试请求数，停止数字payload");
                        break;
                    }
                    String payloadValue = value + numPayloads[ni];
                    HttpRequest numReq = buildMutatedRequest(req, para, payloadValue);

                    long t1 = System.currentTimeMillis();
                    HttpRequestResponse numResult = sendRequestWithInterval(numReq);
                    long cost = System.currentTimeMillis() - t1;
                    sentRequests++;
                    if (cost > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                    HttpResponse numResp = numResult.response();
                    boolean numOk = (numResp != null && numResp.statusCode() >= 200 && numResp.statusCode() < 300);
                    if (numOk && cost < quickBaselineCost) quickBaselineCost = cost;
                    numLens[ni] = numOk ? numResp.body().length() : 0;

                    int code = numOk ? numResp.statusCode() : 0;
                    HttpRequestResponse numDisplay = buildDisplayMessage(numReq, numResult);
                    LogEntry detail = addDetailEntry(new LogEntry(count.get(), toolFlag, numDisplay,
                            numReq.url().toString(),
                            key, payloadValue, "", requestMd5, (int) cost, "end", code, false));
                    paramEntries.add(detail);
                    numEntries.add(detail);
                }

                boolean nCond1 = Math.abs(numLens[0] - numLens[1]) <= 5;
                boolean nCond2 = Math.abs(numLens[0] - baseRespLen) <= 5;
                boolean nCond3 = Math.abs(numLens[1] - numLens[2]) >= 5;
                numVuln = nCond1 && nCond2 && nCond3;

                appendLog(String.format("  数字测试 [%s] len(base=%d, -0=%d, -0-0=%d, -0-1=%d)",
                        key, baseRespLen, numLens[0], numLens[1], numLens[2]));
            }

            // 逗号拼接检测：,0 / ,xxxxxx / ,1
            boolean commaVuln = false;
            {
                String[] commaPayloads = {",0", ",xxxxxx", ",1"};
                int[] commaLens = new int[3];

                for (int ci = 0; ci < 3; ci++) {
                    if (sentRequests >= MAX_REQUESTS_PER_PARAM) {
                        appendLog(scanId + " 参数=" + key + " 达到最大测试请求数，停止逗号payload");
                        break;
                    }
                    String payloadValue = value + commaPayloads[ci];
                    HttpRequest commaReq = buildMutatedRequest(req, para, payloadValue);

                    long t1 = System.currentTimeMillis();
                    HttpRequestResponse commaResult = sendRequestWithInterval(commaReq);
                    long cost = System.currentTimeMillis() - t1;
                    sentRequests++;
                    if (cost > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                    HttpResponse commaResp = commaResult.response();
                    boolean commaOk = (commaResp != null && commaResp.statusCode() >= 200 && commaResp.statusCode() < 300);
                    if (commaOk && cost < quickBaselineCost) quickBaselineCost = cost;
                    commaLens[ci] = commaOk ? commaResp.body().length() : 0;

                    int code = commaOk ? commaResp.statusCode() : 0;
                    HttpRequestResponse commaDisplay = buildDisplayMessage(commaReq, commaResult);
                    LogEntry detail = addDetailEntry(new LogEntry(count.get(), toolFlag, commaDisplay,
                            commaReq.url().toString(),
                            key, payloadValue, "", requestMd5, (int) cost, "end", code, false));
                    paramEntries.add(detail);
                    commaEntries.add(detail);
                }

                boolean cCond1 = Math.abs(commaLens[2] - commaLens[0]) < 6;
                boolean cCond2 = Math.abs(commaLens[0] - commaLens[1]) >= 6;
                commaVuln = cCond1 && cCond2;
                appendLog(String.format("  逗号判定 [%s] cond1(|,1-,0|<6)=%s cond2(|,0-,xxxxxx|>=6)=%s result=%s",
                        key, cCond1, cCond2, commaVuln));

                appendLog(String.format("  逗号测试 [%s] len(base=%d, ,0=%d, ,xxxxxx=%d, ,1=%d)",
                        key, baseRespLen, commaLens[0], commaLens[1], commaLens[2]));
            }

            boolean expVuln = false;
            boolean divVuln = false;
            boolean sleepVuln = false;

            // 报错注入检测（对四个 payload 的响应逐一检测）
            boolean errorVuln = false;
            String  errorSign = "";
            if (!compiledErrorPatterns.isEmpty()) {
                outer:
                for (int qi = 0; qi < 4; qi++) {
                    if (quoteResults[qi] == null) continue;
                    HttpResponse qResp = quoteResults[qi].response();
                    if (qResp == null) continue;
                    String respBody = qResp.bodyToString();
                    String matchedPattern = findMatchedErrorPattern(respBody);
                    if (matchedPattern != null) {
                        String shortPat = matchedPattern.length() > 20 ? matchedPattern.substring(0, 20) + "..." : matchedPattern;
                        errorSign = "✔ 报错:" + shortPat;
                        errorVuln = true;
                        appendLog("【报错注入】参数:" + key
                                + " payload:" + value + quotePayloads[qi]
                                + " 匹配:" + matchedPattern);
                        break outer;
                    }
                }
            }

            // 分级检测：快速规则命中后，跳过重型规则(exp/div/sleep)
            boolean fastRuleHit = quoteVuln || numVuln || commaVuln || errorVuln;
            if (!fastRuleHit && !slowDetected && sentRequests < MAX_REQUESTS_PER_PARAM) {
                // Oracle exp 检测：'||exp(200)||' / '||exp(11111)||'
                String[] expPayloads = {"'||exp(200)||'", "'||exp(11111)||'"};
                int[] expLens = new int[2];
                for (int ei = 0; ei < 2; ei++) {
                    if (sentRequests >= MAX_REQUESTS_PER_PARAM) {
                        appendLog(scanId + " 参数=" + key + " 达到最大测试请求数，停止exp payload");
                        break;
                    }
                    String payloadValue = value + expPayloads[ei];
                    HttpRequest expReq = buildMutatedRequest(req, para, payloadValue);
                    long t1 = System.currentTimeMillis();
                    HttpRequestResponse expResult = sendRequestWithInterval(expReq);
                    long cost = System.currentTimeMillis() - t1;
                    sentRequests++;
                    if (cost > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                    HttpResponse expResp = expResult.response();
                    boolean expOk = (expResp != null && expResp.statusCode() >= 200 && expResp.statusCode() < 300);
                    if (expOk && cost < quickBaselineCost) quickBaselineCost = cost;
                    expLens[ei] = expOk ? expResp.body().length() : 0;
                    int code = expOk ? expResp.statusCode() : 0;
                    HttpRequestResponse expDisplay = buildDisplayMessage(expReq, expResult);
                    LogEntry detail = addDetailEntry(new LogEntry(count.get(), toolFlag, expDisplay,
                            expReq.url().toString(),
                            key, payloadValue, "", requestMd5, (int) cost, "end", code, false));
                    paramEntries.add(detail);
                    expEntries.add(detail);
                }
                boolean eCond1 = Math.abs(expLens[0] - baseRespLen) <= 15;
                boolean eCond2 = Math.abs(expLens[1] - expLens[0]) >= 15;
                expVuln = eCond1 && eCond2;
                appendLog(String.format("  exp测试 [%s] len(base=%d, exp200=%d, exp11111=%d)",
                        key, baseRespLen, expLens[0], expLens[1]));

                // 除零检测：'||1/0||' / '||1/1||'
                String[] divPayloads = {"'||1/0||'", "'||1/1||'"};
                int[] divLens = new int[2];
                for (int di = 0; di < 2; di++) {
                    if (sentRequests >= MAX_REQUESTS_PER_PARAM) {
                        appendLog(scanId + " 参数=" + key + " 达到最大测试请求数，停止除零payload");
                        break;
                    }
                    String payloadValue = value + divPayloads[di];
                    HttpRequest divReq = buildMutatedRequest(req, para, payloadValue);
                    long t1 = System.currentTimeMillis();
                    HttpRequestResponse divResult = sendRequestWithInterval(divReq);
                    long cost = System.currentTimeMillis() - t1;
                    sentRequests++;
                    if (cost > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                    HttpResponse divResp = divResult.response();
                    boolean divOk = (divResp != null && divResp.statusCode() >= 200 && divResp.statusCode() < 300);
                    if (divOk && cost < quickBaselineCost) quickBaselineCost = cost;
                    divLens[di] = divOk ? divResp.body().length() : 0;
                    int code = divOk ? divResp.statusCode() : 0;
                    HttpRequestResponse divDisplay = buildDisplayMessage(divReq, divResult);
                    LogEntry detail = addDetailEntry(new LogEntry(count.get(), toolFlag, divDisplay,
                            divReq.url().toString(),
                            key, payloadValue, "", requestMd5, (int) cost, "end", code, false));
                    paramEntries.add(detail);
                    divEntries.add(detail);
                }
                boolean dCond1 = Math.abs(divLens[1] - baseRespLen) <= 10;
                boolean dCond2 = Math.abs(divLens[1] - divLens[0]) >= 10;
                divVuln = dCond1 && dCond2;
                appendLog(String.format("  除零测试 [%s] len(base=%d, 1/0=%d, 1/1=%d)",
                        key, baseRespLen, divLens[0], divLens[1]));

                // 延时注入检测：) and sleep(5) and (1=1
                if (sentRequests < MAX_REQUESTS_PER_PARAM) {
                    String sleepPayload = ") and sleep(5) and (1=1";
                    String payloadValue = value + sleepPayload;
                    HttpRequest sleepReq = buildMutatedRequest(req, para, payloadValue);
                    long t1 = System.currentTimeMillis();
                    HttpRequestResponse sleepResult = sendRequestWithInterval(sleepReq);
                    long cost = System.currentTimeMillis() - t1;
                    sentRequests++;
                    if (cost > SINGLE_REQUEST_SLOW_MS) slowDetected = true;
                    HttpResponse sleepResp = sleepResult.response();
                    boolean sleepOk = (sleepResp != null && sleepResp.statusCode() >= 200 && sleepResp.statusCode() < 300);
                    int code = sleepOk ? sleepResp.statusCode() : 0;
                    HttpRequestResponse sleepDisplay = buildDisplayMessage(sleepReq, sleepResult);
                    LogEntry detail = addDetailEntry(new LogEntry(count.get(), toolFlag, sleepDisplay,
                            sleepReq.url().toString(),
                            key, payloadValue, "", requestMd5, (int) cost, "end", code, false));
                    paramEntries.add(detail);
                    sleepEntries.add(detail);
                    sleepVuln = cost > 5000 && quickBaselineCost < 2000;
                    appendLog(String.format("  延时测试 [%s] cost(base=%dms, sleep=%dms)",
                            key, quickBaselineCost == Long.MAX_VALUE ? -1 : quickBaselineCost, cost));
                }
            } else {
                appendLog(scanId + " 参数=" + key + " 快速规则命中或请求偏慢，跳过 exp/div/sleep 检测");
            }

            // 自定义 payload 检测（附加 payload，独立发送）
            boolean diyVuln = false;
            String  diySign = "";
            if (jTextAreaInt == 1) {
                for (String payload : jTextAreaData1.split("\n")) {
                    if (sentRequests >= MAX_REQUESTS_PER_PARAM) {
                        appendLog(scanId + " 参数=" + key + " 达到最大测试请求数，停止diy payload");
                        break;
                    }
                    if (slowDetected) {
                        appendLog(scanId + " 参数=" + key + " 请求偏慢，跳过剩余diy payload");
                        break;
                    }
                    payload = payload.trim();
                    if (payload.isEmpty()) continue;

                    String useValue = (diyPayload2 == 1) ? "" : value;
                    HttpRequest diyReq;
                    long t1 = System.currentTimeMillis();
                    diyReq = buildMutatedRequest(req, para, useValue + payload);
                    HttpRequestResponse diyResult = sendRequestWithInterval(diyReq);
                    long cost = System.currentTimeMillis() - t1;
                    sentRequests++;
                    if (cost > SINGLE_REQUEST_SLOW_MS) slowDetected = true;

                    HttpResponse diyResp = diyResult.response();
                    boolean diyOk = (diyResp != null && diyResp.statusCode() >= 200 && diyResp.statusCode() < 300);
                    int code = diyOk ? diyResp.statusCode() : 0;
                    String diyChangeSign = "";

                    if (cost >= 3000) {
                        diyChangeSign = "time > 3s";
                        diyVuln = true;
                        diySign = diyChangeSign;
                        appendLog("【时间注入】参数:" + key + " payload:" + useValue + payload);
                    }

                    // 报错检测也对自定义 payload 生效
                    if (!diyVuln && !compiledErrorPatterns.isEmpty() && diyOk) {
                        String respBody = diyResp.bodyToString();
                        String matchedPattern = findMatchedErrorPattern(respBody);
                        if (matchedPattern != null) {
                            String shortPat = matchedPattern.length() > 20 ? matchedPattern.substring(0, 20) + "..." : matchedPattern;
                            diyChangeSign = "✔ 报错:" + shortPat;
                            diyVuln = true;
                            diySign = diyChangeSign;
                            appendLog("【报错注入-diy】参数:" + key
                                    + " payload:" + useValue + payload
                                    + " 匹配:" + matchedPattern);
                        }
                    }

                    HttpRequestResponse diyDisplay = buildDisplayMessage(diyReq, diyResult);
                    LogEntry detail = addDetailEntry(new LogEntry(count.get(), toolFlag, diyDisplay,
                            diyReq.url().toString(),
                            key, useValue + payload, diyChangeSign, requestMd5, (int) cost, "end", code, false));
                    paramEntries.add(detail);
                    diyEntries.add(detail);
                }
            }

            // ── 汇总当前参数结论 ────────────────────────────
            boolean paramVuln = quoteVuln || numVuln || commaVuln || expVuln || divVuln || sleepVuln || errorVuln || diyVuln;
            List<String> triggeredSigns = new ArrayList<>();
            if (quoteVuln) {
                triggeredSigns.add("✔ 单引号拼接注入");
                appendLog(String.format("【单引号拼接注入】参数:%s  条件: ①|%d-%d|<=5 ②|%d-%d|<=5 ③|%d-%d|>5",
                        key, len2, len4, len1, len3, len1, len2));
            }
            if (numVuln) {
                triggeredSigns.add("✔ 数字拼接注入(-0/-0-0/-0-1)");
                appendLog("【数字拼接注入】参数:" + key + " 触发 -0/-0-0/-0-1 规则");
            }
            if (commaVuln) {
                triggeredSigns.add("✔ 逗号拼接注入(,0/,xxxxxx/,1)");
                appendLog("【逗号拼接注入】参数:" + key + " 触发 ,0/,xxxxxx/,1 规则");
            }
            if (expVuln) {
                triggeredSigns.add("✔ 表达式注入(exp)");
                appendLog("【表达式注入】参数:" + key + " 触发 exp(200)/exp(11111) 规则");
            }
            if (divVuln) {
                triggeredSigns.add("✔ 表达式注入(除零)");
                appendLog("【表达式注入】参数:" + key + " 触发 1/0 与 1/1 规则");
            }
            if (sleepVuln) {
                triggeredSigns.add("✔ 延时注入(sleep)");
                appendLog("【延时注入】参数:" + key + " 触发 sleep(5) 规则");
            }
            if (errorVuln) triggeredSigns.add(errorSign);
            if (diyVuln)   triggeredSigns.add(diySign);

            String paramSign = String.join(" | ", triggeredSigns);

            if (paramVuln) {
                changeSign1 = " ✔";
                anyVulnFound = true;
                appendLog("【疑似注入】URL:" + req.url() + " 参数:" + key + " 结论:" + paramSign);
            }

            if (paramVuln) {
                if (quoteVuln) markEntries(quoteEntries, "✔ 单引号拼接注入");
                if (numVuln) markEntries(numEntries, "✔ 数字拼接注入(-0/-0-0/-0-1)");
                if (commaVuln) markEntries(commaEntries, "✔ 逗号拼接注入(,0/,xxxxxx/,1)");
                if (expVuln) markEntries(expEntries, "✔ 表达式注入(exp)");
                if (divVuln) markEntries(divEntries, "✔ 表达式注入(除零)");
                if (sleepVuln) markEntries(sleepEntries, "✔ 延时注入(sleep)");
                if (errorVuln) markEntries(quoteEntries, errorSign);
                if (diyVuln) markEntries(diyEntries, diySign);

                for (LogEntry entry : paramEntries) {
                    entry.isVulnRow = true;
                }
            }
        }

        // 更新主表该行状态
        final String sign = changeSign1;
        final boolean vuln = anyVulnFound;
        synchronized (log) {
            for (LogEntry entry : log) {
                if (requestMd5.equals(entry.dataMd5)) {
                    entry.state     = "end!" + sign;
                    entry.isVulnRow = vuln;
                }
            }
        }
        if (requestMd5.equals(dataMd5Id)) {
            requestDetailRefresh();
        }
        appendLog(scanId + " 检测完成 URL=" + req.url() + " 结果=" + (vuln ? "疑似注入" : "未命中"));
        SwingUtilities.invokeLater(this::fireTableDataChanged);
    }

    // =========================================================
    // 日志追加
    // =========================================================
    private void appendLog(String msg) {
        stdout.println(msg);
        if (logTextArea != null) {
            SwingUtilities.invokeLater(() -> {
                logTextArea.append(msg + "\n");
                logTextArea.setCaretPosition(logTextArea.getDocument().getLength());
            });
        }
    }

    private void refreshCompiledErrorPatterns() {
        List<Pattern> compiled = new ArrayList<>();
        for (String pat : diyErrorText.split("\n")) {
            String v = pat.trim();
            if (v.isEmpty()) continue;
            try {
                compiled.add(Pattern.compile(v, Pattern.DOTALL | Pattern.CASE_INSENSITIVE));
            } catch (Exception ignored) {}
        }
        compiledErrorPatterns = compiled;
    }

    private String findMatchedErrorPattern(String respBody) {
        for (Pattern p : compiledErrorPatterns) {
            if (p.matcher(respBody).find()) {
                return p.pattern();
            }
        }
        return null;
    }

    private HttpRequestResponse sendRequestWithInterval(HttpRequest req) {
        synchronized (sendLock) {
            int interval = requestIntervalMs;
            if (interval > 0) {
                long now = System.currentTimeMillis();
                long last = lastSendAt.get();
                long waitMs = interval - (now - last);
                if (waitMs > 0) {
                    try {
                        Thread.sleep(waitMs);
                    } catch (InterruptedException ie) {
                        Thread.currentThread().interrupt();
                    }
                }
            }
            HttpRequestResponse result = http.sendRequest(req);
            lastSendAt.set(System.currentTimeMillis());
            return result;
        }
    }

    private HttpRequestResponse buildDisplayMessage(HttpRequest sentRequest, HttpRequestResponse actualResult) {
        return HttpRequestResponse.httpRequestResponse(sentRequest, actualResult.response());
    }

    private String extractHost(String url) {
        try {
            URI uri = URI.create(url);
            String h = uri.getHost();
            if (h != null && !h.trim().isEmpty()) return h.toLowerCase();
        } catch (Exception ignored) {}
        try {
            String u = url;
            int schemeIdx = u.indexOf("://");
            if (schemeIdx >= 0) u = u.substring(schemeIdx + 3);
            int slash = u.indexOf('/');
            if (slash >= 0) u = u.substring(0, slash);
            int colon = u.indexOf(':');
            if (colon >= 0) u = u.substring(0, colon);
            return u.toLowerCase();
        } catch (Exception ignored) {
            return "";
        }
    }

    private boolean isWhitelistedHost(String host, String rules) {
        String h = host == null ? "" : host.trim().toLowerCase();
        if (h.isEmpty()) return false;
        if (rules == null || rules.trim().isEmpty()) return true;

        for (String raw : rules.split(",")) {
            String rule = raw.trim().toLowerCase();
            if (rule.isEmpty()) continue;
            if (matchesWhiteRule(h, rule)) return true;
        }
        return false;
    }

    private boolean matchesWhiteRule(String host, String rule) {
        if ("*".equals(rule) || "all".equals(rule)) return true;
        if (rule.startsWith("*.")) {
            String root = rule.substring(2);
            return host.equals(root) || host.endsWith("." + root);
        }
        return host.equals(rule);
    }

    private LogEntry addDetailEntry(LogEntry entry) {
        synchronized (log2) {
            log2.add(entry);
        }

        String selectedMd5 = dataMd5Id;
        if (selectedMd5 != null && selectedMd5.equals(entry.dataMd5)) {
            synchronized (log3) {
                log3.add(entry);
            }
            requestDetailRefresh();
        }
        return entry;
    }

    private void requestDetailRefresh() {
        if (detailRefreshPending.incrementAndGet() > 1) {
            return;
        }
        SwingUtilities.invokeLater(() -> {
            detailRefreshPending.set(0);
            model.fireTableDataChanged();
        });
    }

    private void markEntries(List<LogEntry> entries, String sign) {
        for (LogEntry entry : entries) {
            if (entry.change == null || entry.change.trim().isEmpty()) {
                entry.change = sign;
            } else if (!entry.change.contains(sign)) {
                entry.change = entry.change + " | " + sign;
            }
            entry.isVulnRow = true;
        }
    }

    private HttpRequest buildMutatedRequest(HttpRequest req, ParsedHttpParameter target, String newValue) {
        HttpParameterType type = target.type();
        boolean jsonLike = (type == HttpParameterType.JSON || isJsonBody(req));
        boolean xmlLike = isXmlBody(req);

        if (jsonLike && isChunkedTransfer(req)) {
            return req;
        }
        if (xmlLike && isChunkedTransfer(req)) {
            return req;
        }

        if (jsonLike) {
            HttpRequest jsonReq = buildJsonRequest(req, target.name(), newValue);
            if (jsonReq != req) return normalizeBodyFraming(jsonReq);
            return req;
        }
        if (xmlLike) {
            HttpRequest xmlReq = buildXmlRequest(req, target.name(), newValue);
            if (xmlReq != req) return normalizeBodyFraming(xmlReq);
            return req;
        }

        return req.withUpdatedParameters(HttpParameter.parameter(target.name(), newValue, type));
    }

    private HttpRequest buildJsonRequest(HttpRequest req, String fieldName, String newValue) {
        String body = req.bodyToString();
        String key = Pattern.quote(fieldName);
        String escaped = escapeJson(newValue);

        Pattern quotedValue = Pattern.compile("(\\\"" + key + "\\\"\\s*:\\s*\\\")((?:\\\\.|[^\\\"\\\\])*)(\\\")");
        Matcher quotedMatcher = quotedValue.matcher(body);
        if (quotedMatcher.find()) {
            String replacement = quotedMatcher.group(1) + Matcher.quoteReplacement(escaped) + quotedMatcher.group(3);
            return req.withBody(quotedMatcher.replaceFirst(Matcher.quoteReplacement(replacement)));
        }

        Pattern primitiveValue = Pattern.compile("(\\\"" + key + "\\\"\\s*:\\s*)(-?\\d+(?:\\.\\d+)?|true|false|null)");
        Matcher primitiveMatcher = primitiveValue.matcher(body);
        if (primitiveMatcher.find()) {
            String replacement = primitiveMatcher.group(1) + "\"" + Matcher.quoteReplacement(escaped) + "\"";
            return req.withBody(primitiveMatcher.replaceFirst(Matcher.quoteReplacement(replacement)));
        }
        return req;
    }

    private HttpRequest buildXmlRequest(HttpRequest req, String fieldName, String newValue) {
        String body = req.bodyToString();
        String tag = Pattern.quote(fieldName);
        Pattern element = Pattern.compile("(<\\s*" + tag + "\\s*>)([\\s\\S]*?)(<\\s*/\\s*" + tag + "\\s*>)", Pattern.CASE_INSENSITIVE);
        Matcher matcher = element.matcher(body);
        if (matcher.find()) {
            String replacement = matcher.group(1)
                    + Matcher.quoteReplacement(escapeXml(newValue))
                    + matcher.group(3);
            return req.withBody(matcher.replaceFirst(Matcher.quoteReplacement(replacement)));
        }
        return req;
    }

    private boolean isJsonBody(HttpRequest req) {
        String ct = req.headerValue("Content-Type");
        if (ct != null && ct.toLowerCase().contains("application/json")) return true;
        String body = req.bodyToString().trim();
        return body.startsWith("{") || body.startsWith("[");
    }

    private boolean isXmlBody(HttpRequest req) {
        String ct = req.headerValue("Content-Type");
        if (ct != null) {
            String lower = ct.toLowerCase();
            if (lower.contains("application/xml") || lower.contains("text/xml")) return true;
        }
        return req.bodyToString().trim().startsWith("<");
    }

    private boolean isChunkedTransfer(HttpRequest req) {
        String te = req.headerValue("Transfer-Encoding");
        return te != null && te.toLowerCase().contains("chunked");
    }

    private HttpRequest normalizeBodyFraming(HttpRequest req) {
        HttpRequest normalized = req.withBody(req.bodyToString());
        normalized = tryInvokeRequestMethod(normalized, "withRemovedHeader", "Transfer-Encoding");
        normalized = tryInvokeRequestMethod(normalized, "withRemovedHeader", "transfer-encoding");

        int contentLength = normalized.bodyToString().getBytes(StandardCharsets.UTF_8).length;
        String lenValue = String.valueOf(contentLength);

        HttpRequest updated = tryInvokeRequestMethod(normalized, "withUpdatedHeader", "Content-Length", lenValue);
        if (updated == normalized) {
            updated = tryInvokeRequestMethod(normalized, "withAddedHeader", "Content-Length", lenValue);
        }
        return updated;
    }

    private HttpRequest tryInvokeRequestMethod(HttpRequest req, String methodName, String arg1) {
        try {
            Method m = req.getClass().getMethod(methodName, String.class);
            Object ret = m.invoke(req, arg1);
            if (ret instanceof HttpRequest) return (HttpRequest) ret;
        } catch (Exception ignored) {}
        return req;
    }

    private HttpRequest tryInvokeRequestMethod(HttpRequest req, String methodName, String arg1, String arg2) {
        try {
            Method m = req.getClass().getMethod(methodName, String.class, String.class);
            Object ret = m.invoke(req, arg1, arg2);
            if (ret instanceof HttpRequest) return (HttpRequest) ret;
        } catch (Exception ignored) {}
        return req;
    }

    private String escapeJson(String value) {
        return value
                .replace("\\", "\\\\")
                .replace("\"", "\\\"")
                .replace("\n", "\\n")
                .replace("\r", "\\r")
                .replace("\t", "\\t");
    }

    private String escapeXml(String value) {
        return value
                .replace("&", "&amp;")
                .replace("<", "&lt;")
                .replace(">", "&gt;")
                .replace("\"", "&quot;")
                .replace("'", "&apos;");
    }

    // =========================================================
    // MD5
    // =========================================================
    private String md5(String key) {
        char[] hex = {'0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F'};
        try {
            MessageDigest md     = MessageDigest.getInstance("MD5");
            byte[]        digest = md.digest(key.getBytes(StandardCharsets.UTF_8));
            StringBuilder sb     = new StringBuilder();
            for (byte b : digest) {
                sb.append(hex[(b >>> 4) & 0xF]).append(hex[b & 0xF]);
            }
            return sb.toString();
        } catch (Exception e) { return ""; }
    }

    // =========================================================
    // 主表模型方法
    // =========================================================
    public int getRowCount() {
        synchronized (log) {
            return log.size();
        }
    }
    public int    getColumnCount() { return 5; }

    public String getColumnName(int column) {
        switch (column) {
            case 0: return "#";
            case 1: return "来源";
            case 2: return "URL";
            case 3: return "长度";
            case 4: return "状态";
            default: return "";
        }
    }

    public Object getValueAt(int row, int column) {
        LogEntry e;
        synchronized (log) {
            if (row < 0 || row >= log.size()) return "";
            e = log.get(row);
        }
        switch (column) {
            case 0: return e.id;
            case 1: return e.toolFlag == 1024 ? "手动发送" : ("Tool:" + e.toolFlag);
            case 2: return e.url;
            case 3: return e.message.response() != null ? e.message.response().body().length() : 0;
            case 4: return e.state;
            default: return "";
        }
    }

    public boolean isVulnRow(int row) {
        synchronized (log) {
            return row >= 0 && row < log.size() && log.get(row).isVulnRow;
        }
    }

    public void fireTableRowsInserted(int first, int last) {
        ((AbstractTableModel) logTable.getModel()).fireTableRowsInserted(first, last);
    }

    public void fireTableDataChanged() {
        ((AbstractTableModel) logTable.getModel()).fireTableDataChanged();
    }

    // =========================================================
    // 内部类
    // =========================================================
    static class RequestMd5 {
        public final String md5Data;
        public RequestMd5(String d) { md5Data = d; }
    }

    static class LogEntry {
        public final int    id;
        public final int    toolFlag;
        public final HttpRequestResponse message;
        public final String url;
        public final String parameter;
        public       String value;
        public       String change;
        public final String dataMd5;
        public final int    times;
        public final int    code;
        public       String state;
        public       boolean isVulnRow; // true = 标黄

        public LogEntry(int id, int toolFlag, HttpRequestResponse message, String url,
                        String parameter, String value, String change, String dataMd5,
                        int times, String state, int code, boolean isVulnRow) {
            this.id         = id;
            this.toolFlag   = toolFlag;
            this.message    = message;
            this.url        = url;
            this.parameter  = parameter;
            this.value      = value;
            this.change     = change;
            this.dataMd5    = dataMd5;
            this.times      = times;
            this.state      = state;
            this.code       = code;
            this.isVulnRow  = isVulnRow;
        }
    }

    // ── 详情表模型 ────────────────────────────────────────────
    class MyModel extends AbstractTableModel {
        @Override
        public int getRowCount() {
            synchronized (log3) {
                return log3.size();
            }
        }
        @Override public int getColumnCount() { return 6; }

        @Override
        public String getColumnName(int col) {
            switch (col) {
                case 0: return "参数";
                case 1: return "payload";
                case 2: return "长度";
                case 3: return "变化";
                case 4: return "用时";
                case 5: return "状态码";
                default: return "";
            }
        }

        @Override
        public Object getValueAt(int row, int col) {
            LogEntry e;
            synchronized (log3) {
                if (row < 0 || row >= log3.size()) return "";
                e = log3.get(row);
            }
            switch (col) {
                case 0: return e.parameter;
                case 1: return e.value;
                case 2: return e.message.response() != null ? e.message.response().body().length() : 0;
                case 3: return e.change;
                case 4: return e.times;
                case 5: return e.code;
                default: return "";
            }
        }
    }

    // ── 主列表（带黄色高亮渲染器）────────────────────────────
    class Table extends JTable {
        public Table(BurpExtender m) {
            super(new AbstractTableModel() {
                @Override public int    getRowCount()            { return m.getRowCount(); }
                @Override public int    getColumnCount()         { return m.getColumnCount(); }
                @Override public String getColumnName(int c)     { return m.getColumnName(c); }
                @Override public Object getValueAt(int r, int c) { return m.getValueAt(r, c); }
            });

            // 黄色高亮：存在注入的行整行标黄
            DefaultTableCellRenderer renderer = new DefaultTableCellRenderer() {
                @Override
                public Component getTableCellRendererComponent(
                        JTable table, Object value, boolean isSelected,
                        boolean hasFocus, int row, int column) {
                    Component c = super.getTableCellRendererComponent(
                            table, value, isSelected, hasFocus, row, column);
                    if (!isSelected) {
                        c.setBackground(m.isVulnRow(row)
                                ? new Color(255, 255, 0)   // 注入行 → 黄色
                                : Color.WHITE);
                    }
                    return c;
                }
            };
            // 对所有列应用该渲染器
            for (int i = 0; i < getColumnCount(); i++) {
                getColumnModel().getColumn(i).setCellRenderer(renderer);
            }
        }

        @Override
        public void changeSelection(int row, int col, boolean toggle, boolean extend) {
            LogEntry entry;
            synchronized (log) {
                if (row < 0 || row >= log.size()) return;
                entry = log.get(row);
            }
            dataMd5Id = entry.dataMd5;

            synchronized (log3) {
                log3.clear();
                synchronized (log2) {
                    for (LogEntry le : log2) {
                        if (le.dataMd5.equals(dataMd5Id)) log3.add(le);
                    }
                }
            }
            model.fireTableDataChanged();

            requestViewer.setRequest(entry.message.request());
            responseViewer.setResponse(entry.message.response());
            super.changeSelection(row, col, toggle, extend);
        }
    }

    // ── 详情列表（prepareRenderer 覆写，黄色高亮，列数无关）──────────────
    class TableLog2 extends JTable {
        public TableLog2(TableModel m) { super(m); }

        @Override
        public Component prepareRenderer(javax.swing.table.TableCellRenderer renderer, int row, int column) {
            Component c = super.prepareRenderer(renderer, row, column);
            if (!isRowSelected(row)) {
                boolean vulnRow = false;
                synchronized (log3) {
                    if (row >= 0 && row < log3.size()) {
                        vulnRow = log3.get(row).isVulnRow;
                    }
                }
                c.setBackground(vulnRow ? new Color(255, 255, 0) : Color.WHITE);
            }
            return c;
        }

        @Override
        public void changeSelection(int row, int col, boolean toggle, boolean extend) {
            LogEntry e = null;
            synchronized (log3) {
                if (row >= 0 && row < log3.size()) {
                    e = log3.get(row);
                }
            }
            if (e != null) {
                requestViewer.setRequest(e.message.request());
                responseViewer.setResponse(e.message.response());
            }
            super.changeSelection(row, col, toggle, extend);
        }
    }
}
