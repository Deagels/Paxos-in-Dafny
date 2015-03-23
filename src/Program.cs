using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading;
using System.Threading.Tasks;
using System.Numerics;
using System.Net;
using System.Net.Sockets;

namespace Paxos_Framework
{
    public static class Program
    {
        static void Main(string[] args)
        {
            Console.WriteLine("#################################### PAXOS #####################################");

            Paxos pxs = new Paxos(24805);

            string[] cmd;
            while (true)
            {
                cmd = Console.ReadLine().Split(' ');
                if (cmd.Length > 0)
                {
                    if (cmd[0] == "port")
                    {
                        if (cmd.Length == 2)
                        {
                            try { pxs.server.UpdatePort(int.Parse(cmd[1])); }
                            catch (Exception) {}
                        }
                        else if (cmd.Length == 1)
                        { pxs.server.AnnounceHost(); }
                    }
                    else if (cmd[0] == "add")
                    {
                        if (cmd.Length > 1)
                        {
                            if (cmd[1] == "proposer")
                            {
                                pxs.pro = new Proposer<int>();
                                pxs.proposers.Add(pxs.localhost);
                                Console.WriteLine("Proposer role added");
                            }
                            else if (cmd[1] == "acceptor")
                            {
                                pxs.acp = new Acceptor<int>();
                                pxs.acceptors.Add(pxs.localhost);
                                Console.WriteLine("Acceptor role added");
                            }
                            else if (cmd[1] == "learner")
                            {
                                pxs.lrn = new Learner<int>();
                                pxs.learners.Add(pxs.localhost);
                                Console.WriteLine("Learner role added");
                            }
                            else if (cmd.Length == 3)
                            {
                                try {
                                    var ip   = IPAddress.Parse( cmd[1] );
                                    var port = int.Parse( cmd[2] );
                                    IPEndPoint peer = new IPEndPoint(ip, port);
                                    pxs.client.Connect( peer );
                                } catch (FormatException) {}
                            }
                        }
                        else if (cmd.Length == 1)
                        { pxs.server.AnnounceHost(); }
                    }
                    else { Console.WriteLine("unknown command"); }
                }
            }
        }

        public static IPAddress LocalIPAddr()
        {
            IPHostEntry host;
            host = Dns.GetHostEntry(Dns.GetHostName());
            foreach (IPAddress ip in host.AddressList)
            {
                if (ip.AddressFamily == AddressFamily.InterNetwork) { return ip; }
            }
            return IPAddress.Parse("127.0.0.1");
        }
    }

    class Paxos
    {
        public Proposer<int> pro;
        public Acceptor<int> acp;
        public Learner<int>  lrn;

        public Server server;
        public Client client;

        public List<IPEndPoint> peers     = new List<IPEndPoint>();
        public List<IPEndPoint> proposers = new List<IPEndPoint>();
        public List<IPEndPoint> acceptors = new List<IPEndPoint>();
        public List<IPEndPoint> learners  = new List<IPEndPoint>();

        public IPEndPoint localhost;

        public Paxos(int port) {
            this.server = new Server(this, port);
            this.client = new Client(this, this.server);
            localhost = new IPEndPoint(IPAddress.Loopback, server.port);
            peers.Add(localhost);
        }
    }

    class Client
    {
        Paxos  pxs;
        Server server;

        public Client(Paxos pxs, Server srv) {
            this.pxs = pxs;
            this.server = srv;
        }

        public void Send(IPEndPoint peer)
        {
            Socket sock = new Socket(AddressFamily.InterNetwork, SocketType.Dgram, ProtocolType.Udp);

            string text = "connect " + Program.LocalIPAddr() + server.port;
            byte[] send_buffer = Encoding.ASCII.GetBytes(text);

            sock.SendTo(send_buffer, peer);
        }

        public void Connect(IPEndPoint peer)
        {
            Socket sock = new Socket(AddressFamily.InterNetwork, SocketType.Dgram, ProtocolType.Udp);

            string text = "connect " + Program.LocalIPAddr() +" "+ server.port;
            byte[] send_buffer = Encoding.ASCII.GetBytes(text);

            sock.SendTo(send_buffer, peer);
        }
    }

    class Server
    {
        public  int       port;
        private Paxos     pxs;
        private UdpClient udpListener;
        private Thread    listenThread;

        public Server(Paxos pxs, int port)
        {
            this.pxs = pxs;
            UpdatePort(port);
            this.udpListener.Client.ReceiveTimeout = 1000; //one second
            this.listenThread = new Thread(new ThreadStart(ListenForClients));
            this.listenThread.Start();
            AnnounceHost();
        }

        public void UpdatePort(int port)
        {
            bool first = true;
            bool failed = true;
            while (failed) {
                try {
                    if (this.udpListener != null) { this.udpListener.Close(); }
                    this.udpListener = new UdpClient(port);
                    this.port = port;
                    failed = false;
                } catch {
                    if (first) {
                        Console.WriteLine("Error: Could not listen at port "+ port);
                        first = false;
                    }
                    if (port < 1024) { port = 1024; }
                    else { port += 1; }
                }
            }
        }

        public void AnnounceHost()
        {
            Console.WriteLine("hosting at " + Program.LocalIPAddr().ToString()
                +" : "+ this.port);
        }

        private void ListenForClients()
        {
            IPEndPoint remote = new IPEndPoint(IPAddress.Any, 0);
            int temp = this.port;
            while (true)
            {
                try {
                    temp = this.port;

                    //blocks until receiving a message or times out
                    Byte[] receiveBytes = this.udpListener.Receive(ref remote);
                    string str = Encoding.ASCII.GetString(receiveBytes);
                    string[] msg = str.Split(' ');

                    Console.WriteLine("Received message: " + str);
                    Console.WriteLine("From " +
                        remote.Address.ToString() + ":" +
                        remote.Port.ToString());

                    if (msg.Length == 3 && msg[0] == "connect")
                    {
                        try
                        {
                            IPAddress ip = IPAddress.Parse(msg[1]);
                            int port = int.Parse(msg[2]);
                            IPEndPoint peer = new IPEndPoint(ip, port);
                            if (pxs.peers.FindIndex( item => item == peer ) >= 0)
                            {
                                pxs.peers.Add(peer);
                                pxs.proposers.Add(peer);
                                pxs.acceptors.Add(peer);
                                pxs.learners.Add(peer);
                                pxs.client.Connect(peer);
                            }
                            Console.WriteLine("connected to " +
                                    ip + ":" + port);
                        }
                        catch { }
                    }
                }
                catch (SocketException)
                {
                    if (temp != this.port) { AnnounceHost(); }
                }
                catch (NullReferenceException)
                {
                    System.Threading.Thread.Sleep(1000);
                }
            }
        }
    }
}
